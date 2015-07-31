(*s Cryptographic game definitions. *)

(*i*)
open Syms
open Expr
open Abbrevs
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Types} *)

(** Variable, adversary, oracle, and hash symbol. *)
type vs  = Vsym.t
type ads = Asym.t
type os  = Osym.t
type hs  = Hsym.t
type ors = Oracle.t
             
type distr = Type.ty * expr list

type lcmd =
    LLet of vs * expr
  | LBind of vs list * hs
  | LSamp of vs * distr
  | LGuard of expr

type obody = lcmd list * Expr.expr

type ohybrid = { odef_less : obody; odef_eq : obody; odef_greater : obody }

type odecl =
  | Odef of obody
  | Ohybrid of ohybrid

val is_hybrid : odecl -> bool

type ohtype = OHless | OHeq | OHgreater
type otype = Onohyb | Ohyb of ohtype

(** Oracle definition. *)
type odef = os * vs list * odecl (*r
  $(o,\vec{x}, \vec{m},e): o(x_1,..,x_l) = [e | m_1, .., m_k]$ *)

type gcmd =
  | GLet    of vs * expr
  | GAssert of expr
  | GSamp   of vs * distr
  | GCall   of vs list * ads * expr * odef list

type gdef = gcmd list

(** An event is just an quantified expression. *)
type quant = EvForall | EvExists
type ev = { ev_quant: quant; ev_binding: (vs list * ors)list; ev_expr:expr }

(** A security experiment consists of a game and an event. *)
type sec_exp = { se_gdef : gdef; se_ev : ev }

(*i ----------------------------------------------------------------------- i*)
(* \hd{Pretty printing} *)

val pp_distr : qual: Osym.t qual -> F.formatter -> Type.ty * expr list -> unit

val pp_v : F.formatter -> Vsym.t -> unit

val pp_binder : qual: Osym.t qual -> F.formatter -> Vsym.t list -> unit

val pp_lcmd : qual: Osym.t qual -> F.formatter -> lcmd -> unit

val pp_ilcmd : nonum:bool -> qual: Osym.t qual -> F.formatter -> int * lcmd -> unit

val pp_lcomp : nonum:bool -> qual: Osym.t qual -> F.formatter -> expr * lcmd list -> unit

val pp_odef : nonum:bool -> F.formatter -> odef -> unit

val pp_ohtype : F.formatter -> ohtype -> unit

val pp_otype : F.formatter -> otype -> unit

val pp_gcmd : nonum:bool -> F.formatter -> gcmd -> unit

val pp_igcmd : F.formatter -> int * gcmd -> unit

val pp_gdef : nonum:bool -> F.formatter -> gdef -> unit

val pp_se_nonum : F.formatter -> sec_exp -> unit

val pp_se : F.formatter -> sec_exp -> unit

val pp_ev : F.formatter -> ev -> unit

val pp_ps : F.formatter -> sec_exp list -> unit

(*i ----------------------------------------------------------------------- i*)
(* \hd{Generic functions} *)

val map_distr_exp : ('a -> 'b) -> 'c * 'a list -> 'c * 'b list

val map_lcmd_exp : (expr -> expr) -> lcmd -> lcmd

val map_odef_exp : (expr -> expr) -> odef -> odef

val map_gcmd_exp : (expr -> expr) -> gcmd -> gcmd

val map_gdef_exp : (expr -> expr) -> gdef -> gcmd list

val map_ev_exp   :  (expr -> expr) -> ev -> ev 

val map_se_exp : (expr -> expr) -> sec_exp -> sec_exp

val iter_distr_exp : ?iexc:bool -> ('a -> unit) -> 'b * 'a list -> unit

val iter_lcmd_exp : ?iexc:bool -> (expr -> unit) -> lcmd -> unit

val iter_odef_exp : ?iexc:bool -> (expr -> unit) -> odef -> unit

val iter_gcmd_exp : ?iexc:bool -> (expr -> unit) -> gcmd -> unit

val iter_gdef_exp : ?iexc:bool -> (expr -> unit) -> gcmd list -> unit

val iter_se_exp :  ?iexc:bool -> (expr -> unit) -> sec_exp -> unit

val fold_union :  ('a -> Se.t) -> 'a list -> Se.t

(*i ----------------------------------------------------------------------- i*)
(*  \hd{Positions and replacement functions} *)

type gcmd_pos = int

type odef_pos = int * int

type ocmd_pos = int * int * int * otype

(* position that points to Eq hybrid oracle, i.e., fourth value is fixed *)
type ocmd_pos_eq = (int * int * int)

val get_se_gcmd : sec_exp -> gcmd_pos -> gcmd

type se_ctxt = { sec_left : gdef; sec_right : gdef; sec_ev : ev; }

val get_se_ctxt_len : sec_exp -> pos:gcmd_pos -> len:int -> gcmd list * se_ctxt

val get_se_ctxt : sec_exp -> gcmd_pos -> gcmd * se_ctxt

val set_se_ctxt : gcmd list -> se_ctxt -> sec_exp

val set_se_gcmd : sec_exp -> gcmd_pos -> gcmd list -> sec_exp

val get_se_lcmd :
  sec_exp -> ocmd_pos -> os * vs list * (lcmd list * lcmd * lcmd list) * expr

type se_octxt = {
  seoc_asym : ads;
  seoc_avars : vs list;
  seoc_aarg : expr;
  seoc_oleft : odef list;
  seoc_oright : odef list;
  seoc_obless : obody option;
  seoc_obeq : obody option;
  seoc_obgreater : obody option;
  seoc_osym : os;
  seoc_oargs: vs list;
  seoc_return : expr;
  seoc_cleft : lcmd list;
  seoc_cright : lcmd list;
  seoc_sec : se_ctxt
}

val get_se_octxt   : sec_exp -> ocmd_pos -> lcmd * se_octxt

val get_se_octxt_len : sec_exp -> ocmd_pos -> int -> lcmd list * se_octxt

val set_se_octxt : lcmd list -> se_octxt -> sec_exp

val set_se_lcmd : sec_exp -> ocmd_pos -> lcmd list -> sec_exp

(* \hd{Iterate with context} *) 

type iter_pos =
  | InEv
  | InMain       of gcmd_pos
  | InOrclReturn of ocmd_pos * Type.ty * Type.ty
  | InOrcl       of ocmd_pos * Type.ty * Type.ty
    (* position, adversary argument type, oracle type *)

val pp_iter_pos : F.formatter -> iter_pos -> unit

type iter_ctx = {
  ic_pos     : iter_pos;
  ic_isZero  : expr list;
  ic_nonZero : expr list
}

val pp_iter_ctx : F.formatter -> iter_ctx -> unit

val iter_ctx_odef_exp :
  Type.ty -> int -> int -> expr list ->
  ?iexc:bool -> (iter_ctx -> expr -> unit) -> odef -> unit

val iter_ctx_gdef_exp :
  ?iexc:bool -> (iter_ctx -> expr -> unit) -> gcmd list -> expr list

val iter_ctx_se_exp :
  ?iexc:bool -> (iter_ctx -> expr -> unit) -> sec_exp -> unit

(*i ----------------------------------------------------------------------- i*)
(*  \hd{Equality} *)

val distr_equal : distr -> distr -> bool

val lcmd_equal : lcmd -> lcmd -> bool

val lcmds_equal : lcmd list -> lcmd list -> bool

val odef_equal : odef -> odef -> bool

val gcmd_equal : gcmd -> gcmd -> bool

val gdef_equal : gdef -> gdef -> bool

val ev_equal   : ev -> ev -> bool

val se_equal : sec_exp -> sec_exp -> bool

(*i ----------------------------------------------------------------------- i*)
(* \hd{Read and write variables} *)

val read_distr : distr -> Se.t

val read_lcmd : lcmd -> Se.t

val read_lcmds : lcmd list -> Se.t

val add_binding : vs list -> Se.t

val write_lcmd : lcmd -> Se.t

val write_lcmds : lcmd list -> Se.t

val read_odef : odef -> Se.t
val read_odefs : odef list -> Se.t

val read_gcmd : gcmd -> Se.t

val read_gcmds : gcmd list -> Se.t

val write_gcmd : gcmd -> Se.t

val write_gcmds : gcmd list -> Se.t

val asym_gcmds : gcmd list -> ads list

val read_se : sec_exp -> Se.t


(*i ----------------------------------------------------------------------- i*)
(* \hd{Hash_calls occurences} *)
val expr_hash_calls : expr -> Hsym.S.t
                          
val gcmd_all_hash_calls : gcmd -> Hsym.S.t

val gdef_all_hash_calls : gdef -> Hsym.S.t

val gdef_global_hash_calls : gdef -> Hsym.S.t
                                       
val expr_hash_calls_h : Hsym.t -> expr -> Se.t
                          
val gcmd_all_hash_calls_h : Hsym.t -> gcmd -> Se.t

val gdef_all_hash_calls_h : Hsym.t -> gdef -> Se.t

val gdef_global_hash_calls_h : Hsym.t -> gdef -> Se.t

(* \hd{Variable occurences} *)
val expr_vars : expr -> Vsym.S.t
                          
val gcmd_all_vars : gcmd -> Vsym.S.t

val gdef_all_vars : gdef -> Vsym.S.t

val gdef_global_vars : gdef -> Vsym.S.t

(*i ----------------------------------------------------------------------- i*)
(* \hd{Variable renaming} *)

val subst_v_e : (vs -> vs) -> expr -> expr
val subst_v_ev : (vs -> vs) -> ev -> ev

val subst_v_lc : (vs -> vs) -> lcmd -> lcmd

val subst_v_odef : (vs -> vs) -> odef -> odef

val subst_v_gc : (vs -> vs) -> gcmd -> gcmd

val subst_v_gdef : (vs -> vs) -> gdef -> gdef

val subst_v_se : (vs -> vs) -> sec_exp -> sec_exp

type renaming = vs Vsym.M.t

val id_renaming : renaming

val unif_se   : sec_exp -> sec_exp -> renaming
val unif_gdef : gdef    -> gdef    -> renaming

val ren_injective : renaming -> bool

val pp_ren : F.formatter -> Vsym.t Vsym.M.t -> unit

(* \hd{check_hash_args rule helper : Replace hash calls by lookups} *)
val subst_lkup_e : ((Hsym.t * expr) -> Hsym.t) -> expr -> expr
val subst_lkup_lc : ((Hsym.t * expr) -> Hsym.t) -> lcmd -> lcmd
val subst_lkup_lcmds : ((Hsym.t * expr) -> Hsym.t) -> lcmd list -> lcmd list

(*i ----------------------------------------------------------------------- i*)
(* \hd{Mappings from strings to variables} *) 

type vmap = (string qual * string,Vsym.t) Hashtbl.t

val merge_vmap : vmap -> vmap -> vmap * (vs -> vs)

val vmap_of_ves : Se.t -> vmap

val vmap_of_globals : gdef -> vmap

val vmap_of_se : sec_exp -> vmap

val vmap_in_orcl : sec_exp -> ocmd_pos -> vmap

(*i ----------------------------------------------------------------------- i*)
(* \hd{Normal forms} *)

val norm_distr : ?norm:(expr -> expr) -> expr Me.t -> distr -> distr

val norm_odef : ?norm:(expr -> expr) -> expr Me.t -> expr Expr.Me.t ref option -> odef -> odef

val norm_gdef : ?norm:(expr -> expr) -> gdef -> gdef * expr Me.t

val norm_se : ?norm:(expr -> expr) -> sec_exp -> sec_exp

(*i ----------------------------------------------------------------------- i*)
(* \hd{Probabilistic polynomial time } *)

val has_log_distr : distr -> bool

val has_log_lcmd : lcmd -> bool

val has_log_lcmds : lcmd list -> bool

val has_log_odef : odef -> bool

val has_log_odecl : odecl -> bool

val has_log_gcmd : gcmd -> bool

val has_log_gcmds : gcmd list -> bool

val is_ppt_distr : distr -> bool

val is_ppt_lcmd : lcmd -> bool

val is_ppt_lcmds : lcmd list -> bool

val is_ppt_odef : odef -> bool

val is_ppt_odecl : odecl -> bool

val is_ppt_gcmd : gcmd -> bool

val is_ppt_gcmds : gcmd list -> bool

val is_ppt_se : sec_exp -> bool

val is_call : gcmd -> bool

val has_call : gcmd list -> bool

val is_assert : gcmd -> bool

val has_assert : gcmd list -> bool

val destr_guard : lcmd -> expr
