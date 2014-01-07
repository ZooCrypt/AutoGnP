(** Cryptographic game definitions. *)

type distr = Type.ty * Expr.expr list

type lcmd =
    LLet of Vsym.t * Expr.expr
  | LBind of Vsym.t list * Hsym.t
  | LSamp of Vsym.t * distr
  | LGuard of Expr.expr

type odef = Osym.t * Vsym.t list * lcmd list * Expr.expr

type gcmd =
    GLet of Vsym.t * Expr.expr
  | GSamp of Vsym.t * distr
  | GCall of Vsym.t list * Asym.t * Expr.expr * odef list

type gdef = gcmd list

type ev = Expr.expr

type judgment = { ju_gdef : gdef; ju_ev : ev; }

val pp_distr : Format.formatter -> 'a Type.gty * 'b Expr.gexpr list -> unit

val pp_v : Format.formatter -> 'a Vsym.gt -> unit

val pp_binder : Format.formatter -> 'a Vsym.gt list -> unit

val pp_lcmd : Format.formatter -> lcmd -> unit

val pp_ilcmd : Format.formatter -> int * lcmd -> unit

val num_list : 'a list -> (int * 'a) list

val pp_lcomp : Format.formatter -> 'a Expr.gexpr * lcmd list -> unit

val pp_odef :
  Format.formatter ->
  'a Osym.gt * 'b Vsym.gt list * lcmd list * 'c Expr.gexpr -> unit

val pp_gcmd : Format.formatter -> gcmd -> unit

val pp_igcmd : Format.formatter -> int * gcmd -> unit

val pp_gdef : Format.formatter -> gcmd list -> unit

val pp_ju : Format.formatter -> judgment -> unit

val pp_ps : Format.formatter -> judgment list -> unit

val map_distr_exp : ('a -> 'b) -> 'c * 'a list -> 'c * 'b list

val map_lcmd_exp : (Expr.expr -> Expr.expr) -> lcmd -> lcmd

val map_odef_exp :
  (Expr.expr -> Expr.expr) ->
  'a * 'b * lcmd list * Expr.expr -> 'a * 'b * lcmd list * Expr.expr

val map_gcmd_exp : (Expr.expr -> Expr.expr) -> gcmd -> gcmd

val map_gdef_exp : (Expr.expr -> Expr.expr) -> gcmd list -> gcmd list

val map_ju_exp : (Expr.expr -> Expr.expr) -> judgment -> judgment

val iter_distr_exp : ('a -> unit) -> 'b * 'a list -> unit

val iter_lcmd_exp : (Expr.expr -> unit) -> lcmd -> unit

val iter_odef_exp :
  (Expr.expr -> unit) -> 'a * 'b * lcmd list * Expr.expr -> unit

val iter_gcmd_exp : (Expr.expr -> unit) -> gcmd -> unit

val iter_gdef_exp : (Expr.expr -> unit) -> gcmd list -> unit

val iter_ju_exp : (Expr.expr -> unit) -> judgment -> unit

val fold_union : ('a -> Expr.Se.t) -> 'a list -> Expr.Se.t

val read_distr : 'a * Expr.expr list -> Expr.Se.t

val read_lcmd : lcmd -> Expr.Se.t

val read_lcmds : lcmd list -> Expr.Se.t

val add_binding : Vsym.t list -> Expr.Se.t

val write_lcmd : lcmd -> Expr.Se.t

val write_lcmds : lcmd list -> Expr.Se.t

val read_odef : 'a * Vsym.t list * lcmd list * Expr.expr -> Expr.Se.t

val read_gcmd : gcmd -> Expr.Se.t

val read_gcmds : gcmd list -> Expr.Se.t

val write_gcmd : gcmd -> Expr.Se.t

val write_gcmds : gcmd list -> Expr.Se.t

val read_ju : judgment -> Expr.Se.t

val has_log_distr : 'a * Expr.expr list -> bool

val has_log_lcmd : lcmd -> bool

val has_log_lcmds : lcmd list -> bool

val has_log_o : 'a * 'b * lcmd list * Expr.expr -> bool

val has_log_gcmd : gcmd -> bool

val has_log_gcmds : gcmd list -> bool

val is_ppt_distr : 'a * Expr.expr list -> bool

val is_ppt_lcmd : lcmd -> bool

val is_ppt_lcmds : lcmd list -> bool

val is_ppt_o : 'a * 'b * lcmd list * Expr.expr -> bool

val is_ppt_gcmd : gcmd -> bool

val is_ppt_gcmds : gcmd list -> bool

val is_ppt_ju : judgment -> bool

val is_call : gcmd -> bool

val has_call : gcmd list -> bool

type gcmd_pos = int

type odef_pos = int * int

type ocmd_pos = int * int * int

val get_ju_gcmd : judgment -> int -> gcmd

type ju_ctxt = { juc_left : gdef; juc_right : gdef; juc_ev : ev; }

val get_ju_ctxt : judgment -> int -> gcmd * ju_ctxt

val set_ju_ctxt : gcmd list -> ju_ctxt -> judgment

val set_ju_gcmd : judgment -> int -> gcmd list -> judgment

val get_ju_lcmd :
  judgment ->
  int * int * int ->
  Osym.t * Vsym.t list * (lcmd list * lcmd * lcmd list) * Expr.expr

type ju_octxt = {
  juoc_asym : Asym.t;
  juoc_avars : Vsym.t list;
  juoc_aarg : Expr.expr;
  juoc_oleft : odef list;
  juoc_oright : odef list;
  juoc_osym : Osym.t;
  juoc_oargs : Vsym.t list;
  juoc_return : Expr.expr;
  juoc_cleft : lcmd list;
  juoc_cright : lcmd list;
  juoc_juc : ju_ctxt;
}

val get_ju_octxt : judgment -> int * int * int -> lcmd * ju_octxt

val set_ju_octxt : lcmd list -> ju_octxt -> judgment

val set_ju_lcmd : judgment -> int * int * int -> lcmd list -> judgment

val d_equal : Type.ty * Expr.expr list -> Type.ty * Expr.expr list -> bool

val lc_equal : lcmd -> lcmd -> bool

val lcs_equal : lcmd list -> lcmd list -> bool

val o_equal :
  Osym.t * Vsym.t list * lcmd list * Expr.expr ->
  Osym.t * Vsym.t list * lcmd list * Expr.expr -> bool

val gc_equal : gcmd -> gcmd -> bool

val gcs_equal : gcmd list -> gcmd list -> bool

val ju_equal : judgment -> judgment -> bool

val gdef_vars : gcmd list -> Expr.Se.t

val ju_vars : judgment -> Expr.Se.t

val norm_expr_def : Expr.expr -> Expr.expr

val norm_distr :
  ?norm:(Expr.expr -> Expr.expr) ->
  Expr.expr Expr.Me.t -> 'a * Expr.expr list -> 'a * Expr.expr list

val norm_odef :
  ?norm:(Expr.expr -> Expr.expr) ->
  Expr.expr Expr.Me.t ->
  'a * 'b * lcmd list * Expr.expr -> 'a * 'b * lcmd list * Expr.expr

val norm_gdef :
  ?norm:(Expr.expr -> Expr.expr) ->
  gcmd list -> gcmd list * Expr.expr Expr.Me.t

val norm_ju : ?norm:(Expr.expr -> Expr.expr) -> judgment -> judgment

val subst_v_e : (IdType.internal Vsym.gt -> Vsym.t) -> Expr.expr -> Expr.expr

val subst_v_lc : (Vsym.t -> Vsym.t) -> lcmd -> lcmd

val subst_v_odef :
  (Vsym.t -> Vsym.t) ->
  'a * Vsym.t list * lcmd list * Expr.expr ->
  'a * Vsym.t list * lcmd list * Expr.expr

val subst_v_gc : (Vsym.t -> Vsym.t) -> gcmd -> gcmd

val subst_v_gdef : (Vsym.t -> Vsym.t) -> gcmd list -> gcmd list
