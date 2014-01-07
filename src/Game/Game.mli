(** Cryptographic game definitions. *)

open Expr
open Format

(* ----------------------------------------------------------------------- *)
(** {1 Types} *)

type distr = Type.ty * expr list

type lcmd =
    LLet of Vsym.t * expr
  | LBind of Vsym.t list * Hsym.t
  | LSamp of Vsym.t * distr
  | LGuard of expr

type odef = Osym.t * Vsym.t list * lcmd list * expr

type gcmd =
    GLet of Vsym.t * expr
  | GSamp of Vsym.t * distr
  | GCall of Vsym.t list * Asym.t * expr * odef list

type gdef = gcmd list

type ev = expr

type judgment = { ju_gdef : gdef; ju_ev : ev; }

(* ----------------------------------------------------------------------- *)
(** {2 Pretty printing} *)

val pp_distr : formatter -> 'a Type.gty * 'b gexpr list -> unit

val pp_v : formatter -> 'a Vsym.gt -> unit

val pp_binder : formatter -> 'a Vsym.gt list -> unit

val pp_lcmd : formatter -> lcmd -> unit

val pp_ilcmd : formatter -> int * lcmd -> unit

val num_list : 'a list -> (int * 'a) list

val pp_lcomp : formatter -> 'a gexpr * lcmd list -> unit

val pp_odef : formatter -> odef -> unit

val pp_gcmd : formatter -> gcmd -> unit

val pp_igcmd : formatter -> int * gcmd -> unit

val pp_gdef : formatter -> gdef -> unit

val pp_ju : formatter -> judgment -> unit

val pp_ps : formatter -> judgment list -> unit

(* ----------------------------------------------------------------------- *)
(** {3 Generic functions} *)

val map_distr_exp : ('a -> 'b) -> 'c * 'a list -> 'c * 'b list

val map_lcmd_exp : (expr -> expr) -> lcmd -> lcmd

val map_odef_exp : (expr -> expr) -> odef -> odef

val map_gcmd_exp : (expr -> expr) -> gcmd -> gcmd

val map_gdef_exp : (expr -> expr) -> gdef -> gcmd list

val map_ju_exp : (expr -> expr) -> judgment -> judgment

val iter_distr_exp : ('a -> unit) -> 'b * 'a list -> unit

val iter_lcmd_exp : (expr -> unit) -> lcmd -> unit

val iter_odef_exp : (expr -> unit) -> odef -> unit

val iter_gcmd_exp : (expr -> unit) -> gcmd -> unit

val iter_gdef_exp : (expr -> unit) -> gcmd list -> unit

val iter_ju_exp : (expr -> unit) -> judgment -> unit

val fold_union : ('a -> Se.t) -> 'a list -> Se.t

(* ----------------------------------------------------------------------- *)
(** {4 Read and write variables} *)

val read_distr : distr -> Se.t

val read_lcmd : lcmd -> Se.t

val read_lcmds : lcmd list -> Se.t

val add_binding : Vsym.t list -> Se.t

val write_lcmd : lcmd -> Se.t

val write_lcmds : lcmd list -> Se.t

val read_odef : odef -> Se.t

val read_gcmd : gcmd -> Se.t

val read_gcmds : gcmd list -> Se.t

val write_gcmd : gcmd -> Se.t

val write_gcmds : gcmd list -> Se.t

val read_ju : judgment -> Se.t

(* ----------------------------------------------------------------------- *)
(** {5 Probabilistic polynomial time } *)

val has_log_distr : distr -> bool

val has_log_lcmd : lcmd -> bool

val has_log_lcmds : lcmd list -> bool

val has_log_o : odef -> bool

val has_log_gcmd : gcmd -> bool

val has_log_gcmds : gcmd list -> bool

val is_ppt_distr : distr -> bool

val is_ppt_lcmd : lcmd -> bool

val is_ppt_lcmds : lcmd list -> bool

val is_ppt_o : odef -> bool

val is_ppt_gcmd : gcmd -> bool

val is_ppt_gcmds : gcmd list -> bool

val is_ppt_ju : judgment -> bool

val is_call : gcmd -> bool

val has_call : gcmd list -> bool

(* ----------------------------------------------------------------------- *)
(** {6 Positions and replacement functions} *)

type gcmd_pos = int

type odef_pos = int * int

type ocmd_pos = int * int * int

val get_ju_gcmd : judgment -> int -> gcmd

type ju_ctxt = { juc_left : gdef; juc_right : gdef; juc_ev : ev; }

val get_ju_ctxt : judgment -> int -> gcmd * ju_ctxt

val set_ju_ctxt : gcmd list -> ju_ctxt -> judgment

val set_ju_gcmd : judgment -> int -> gcmd list -> judgment

val get_ju_lcmd : judgment -> ocmd_pos -> Osym.t * Vsym.t list * (lcmd list * lcmd * lcmd list) * expr

type ju_octxt = {
  juoc_asym : Asym.t;
  juoc_avars : Vsym.t list;
  juoc_aarg : expr;
  juoc_oleft : odef list;
  juoc_oright : odef list;
  juoc_osym : Osym.t;
  juoc_oargs : Vsym.t list;
  juoc_return : expr;
  juoc_cleft : lcmd list;
  juoc_cright : lcmd list;
  juoc_juc : ju_ctxt;
}

val get_ju_octxt : judgment -> ocmd_pos -> lcmd * ju_octxt

val set_ju_octxt : lcmd list -> ju_octxt -> judgment

val set_ju_lcmd : judgment -> ocmd_pos -> lcmd list -> judgment

(* ----------------------------------------------------------------------- *)
(** {7 Equality} *)

val distr_equal : distr -> distr -> bool

val lcmd_equal : lcmd -> lcmd -> bool

val lcmds_equal : lcmd list -> lcmd list -> bool

val odef_equal : odef -> odef -> bool

val gcmd_equal : gcmd -> gcmd -> bool

val gdef_equal : gdef -> gdef -> bool

val ju_equal : judgment -> judgment -> bool

val gdef_vars : gdef -> Se.t

val ju_vars : judgment -> Se.t

(* ----------------------------------------------------------------------- *)
(** {8 Normal forms} *)

val norm_expr_def : expr -> expr

val norm_distr : ?norm:(expr -> expr) -> expr Me.t -> distr -> distr

val norm_odef : ?norm:(expr -> expr) -> expr Me.t -> odef -> odef

val norm_gdef : ?norm:(expr -> expr) -> gdef -> gdef * expr Me.t

val norm_ju : ?norm:(expr -> expr) -> judgment -> judgment

val subst_v_e : (IdType.internal Vsym.gt -> Vsym.t) -> expr -> expr

val subst_v_lc : (Vsym.t -> Vsym.t) -> lcmd -> lcmd

val subst_v_odef : (Vsym.t -> Vsym.t) -> odef -> odef

val subst_v_gc : (Vsym.t -> Vsym.t) -> gcmd -> gcmd

val subst_v_gdef : (Vsym.t -> Vsym.t) -> gdef -> gdef
