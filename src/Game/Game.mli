(*s Cryptographic game definitions. *)

(*i*)
open Syms
open Expr
open Util
open Gsyms
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Types} *)

(** Variable, adversary, oracle, and hash symbol. *)
type vs  = Vsym.t
type ads = Asym.t
type os  = Osym.t
type hs  = Hsym.t

type distr = Type.ty * expr list

type lcmd =
    LLet of vs * expr
  | LBind of vs list * hs
  | LSamp of vs * distr
  | LGuard of expr

type odef = os * vs list * lcmd list * expr

type gcmd =
    GLet of vs * expr
  | GSamp of vs * distr
  | GCall of vs list * ads * expr * odef list

type gdef = gcmd list

type ev = expr

type judgment = { ju_gdef : gdef; ju_ev : ev; }

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Pretty printing} *)

val pp_distr : F.formatter -> Type.ty * expr list -> unit

val pp_v : F.formatter -> Vsym.t -> unit

val pp_binder : F.formatter -> Vsym.t list -> unit

val pp_lcmd : F.formatter -> lcmd -> unit

val pp_ilcmd : F.formatter -> int * lcmd -> unit

val num_list : 'a list -> (int * 'a) list

val pp_lcomp : F.formatter -> expr * lcmd list -> unit

val pp_odef : F.formatter -> odef -> unit

val pp_gcmd : F.formatter -> gcmd -> unit

val pp_igcmd : F.formatter -> int * gcmd -> unit

val pp_gdef : F.formatter -> gdef -> unit

val pp_ju : F.formatter -> judgment -> unit

val pp_ps : F.formatter -> judgment list -> unit

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Generic functions} *)

val map_distr_exp : ('a -> 'b) -> 'c * 'a list -> 'c * 'b list

val map_lcmd_exp : (expr -> expr) -> lcmd -> lcmd

val map_odef_exp : (expr -> expr) -> odef -> odef

val map_gcmd_exp : (expr -> expr) -> gcmd -> gcmd

val map_gdef_exp : (expr -> expr) -> gdef -> gcmd list

val map_ju_exp : (expr -> expr) -> judgment -> judgment

val iter_distr_exp : ?iexc:bool -> ('a -> unit) -> 'b * 'a list -> unit

val iter_lcmd_exp : ?iexc:bool -> (expr -> unit) -> lcmd -> unit

val iter_odef_exp : ?iexc:bool -> (expr -> unit) -> odef -> unit

val iter_gcmd_exp : ?iexc:bool -> (expr -> unit) -> gcmd -> unit

val iter_gdef_exp : ?iexc:bool -> (expr -> unit) -> gcmd list -> unit

val iter_ju_exp :  ?iexc:bool -> (expr -> unit) -> judgment -> unit

val fold_union :  ('a -> Se.t) -> 'a list -> Se.t

(*i ----------------------------------------------------------------------- i*)
(*  \subsection{Positions and replacement functions} *)

type gcmd_pos = int

type odef_pos = int * int

type ocmd_pos = int * int * int

val get_ju_gcmd : judgment -> gcmd_pos -> gcmd

type ju_ctxt = { juc_left : gdef; juc_right : gdef; juc_ev : ev; }

val get_ju_ctxt : judgment -> gcmd_pos -> gcmd * ju_ctxt

val set_ju_ctxt : gcmd list -> ju_ctxt -> judgment

val set_ju_gcmd : judgment -> gcmd_pos -> gcmd list -> judgment

val get_ju_lcmd : judgment -> ocmd_pos -> os * vs list * (lcmd list * lcmd * lcmd list) * expr

type ju_octxt = {
  juoc_asym : ads;
  juoc_avars : vs list;
  juoc_aarg : expr;
  juoc_oleft : odef list;
  juoc_oright : odef list;
  juoc_osym : os;
  juoc_oargs : vs list;
  juoc_return : expr;
  juoc_cleft : lcmd list;
  juoc_cright : lcmd list;
  juoc_juc : ju_ctxt;
}

val get_ju_octxt : judgment -> ocmd_pos -> lcmd * ju_octxt

val set_ju_octxt : lcmd list -> ju_octxt -> judgment

val set_ju_lcmd : judgment -> ocmd_pos -> lcmd list -> judgment

(* \subsection{Iterate with context} *) 

type iter_pos =
  | InEv
  | InMain       of gcmd_pos
  | InOrclReturn of ocmd_pos * Type.ty * Type.ty
  | InOrcl       of ocmd_pos * Type.ty * Type.ty
    (* position, adversary argument type, oracle type *)

val pp_iter_pos : Util.F.formatter -> iter_pos -> unit

type iter_ctx = {
  ic_pos     : iter_pos;
  ic_isZero  : expr list;
  ic_nonZero : expr list
}

val pp_iter_ctx : Util.F.formatter -> iter_ctx -> unit

val iter_ctx_odef_exp :
  Type.ty -> int -> int -> expr list ->
  ?iexc:bool -> (iter_ctx -> expr -> unit) -> odef -> unit

val iter_ctx_gdef_exp :
  ?iexc:bool -> (iter_ctx -> expr -> unit) -> gcmd list -> expr list

val iter_ctx_ju_exp :
  ?iexc:bool -> (iter_ctx -> expr -> unit) -> judgment -> unit

(*i ----------------------------------------------------------------------- i*)
(*  \subsection{Equality} *)

val distr_equal : distr -> distr -> bool

val lcmd_equal : lcmd -> lcmd -> bool

val lcmds_equal : lcmd list -> lcmd list -> bool

val odef_equal : odef -> odef -> bool

val gcmd_equal : gcmd -> gcmd -> bool

val gdef_equal : gdef -> gdef -> bool

val ju_equal : judgment -> judgment -> bool

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Read and write variables} *)

val read_distr : distr -> Se.t

val read_lcmd : lcmd -> Se.t

val read_lcmds : lcmd list -> Se.t

val add_binding : vs list -> Se.t

val write_lcmd : lcmd -> Se.t

val write_lcmds : lcmd list -> Se.t

val read_odef : odef -> Se.t

val read_gcmd : gcmd -> Se.t

val read_gcmds : gcmd list -> Se.t

val write_gcmd : gcmd -> Se.t

val write_gcmds : gcmd list -> Se.t

val asym_gcmds : gcmd list -> ads list

val read_ju : judgment -> Se.t

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Variable occurences} *)

val gcmd_all_vars : gcmd -> Vsym.S.t

val gdef_all_vars : gdef -> Vsym.S.t

val gdef_global_vars : gdef -> Se.t

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Variable renaming} *)

val subst_v_e : (vs -> vs) -> expr -> expr

val subst_v_lc : (vs -> vs) -> lcmd -> lcmd

val subst_v_odef : (vs -> vs) -> odef -> odef

val subst_v_gc : (vs -> vs) -> gcmd -> gcmd

val subst_v_gdef : (vs -> vs) -> gdef -> gdef

val subst_v_ju : (vs -> vs) -> judgment -> judgment

type renaming = vs Vsym.M.t

val id_renaming : renaming

val unif_ju : judgment -> judgment -> renaming

val ren_injective : renaming -> bool

val pp_ren : F.formatter -> Vsym.t Vsym.M.t -> unit

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Mappings from strings to variables} *) 

type vmap = (string,Vsym.t) Hashtbl.t

val merge_vmap : vmap -> vmap -> vmap * (vs -> vs)

val vmap_of_ves : Se.t -> vmap

val vmap_of_globals : gdef -> vmap

val vmap_of_all : gdef -> vmap

val vmap_in_orcl : judgment -> ocmd_pos -> vmap

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Normal forms} *)

val norm_distr : ?norm:(expr -> expr) -> expr Me.t -> distr -> distr

val norm_odef : ?norm:(expr -> expr) -> expr Me.t -> odef -> odef

val norm_gdef : ?norm:(expr -> expr) -> gdef -> gdef * expr Me.t

val norm_ju : ?norm:(expr -> expr) -> judgment -> judgment

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Probabilistic polynomial time } *)

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

val destr_guard : lcmd -> expr
