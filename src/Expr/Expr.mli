(** Typed algebraic expression: We distinguish
    internal/hashconsed and exported expressions.  *)
open Type
open Format

(* ----------------------------------------------------------------------- *)
(** {1 Expressions} *)
type 'a proj_type = 'a Type.gty * 'a Type.gty * 'a Type.gty

type cnst = GGen | FZ | Z | FOne | B of bool

val cnst_hash : cnst -> int

type op =
    GMult
  | GExp
  | GLog
  | EMap
  | GTMult
  | GTExp
  | GTLog
  | FOpp
  | FMinus
  | FInv
  | FDiv
  | Eq
  | Not
  | Ifte

val op_hash : op -> int

type naryop = FPlus | FMult | Xor | Land

val naryop_hash : naryop -> int

type 'a gexpr = { e_node : 'a gexpr_node; e_ty : 'a Type.gty; e_tag : int; }
and 'a gexpr_node =
    V of 'a Vsym.gt
  | H of 'a Hsym.gt * 'a gexpr
  | Tuple of 'a gexpr list
  | Proj of int * 'a gexpr
  | Cnst of cnst
  | App of op * 'a gexpr list
  | Nary of naryop * 'a gexpr list
  | ElemH of 'a gexpr * 'a Hsym.gt

type expr = IdType.internal gexpr

type expr_node = IdType.internal gexpr_node

type eexpr = IdType.exported gexpr

type eexpr_node = IdType.exported gexpr_node

val e_equal : expr -> expr -> bool
val e_hash : expr -> int
val e_compare : expr -> expr -> int

module Hse : Hashcons.S with type t = expr

val mk_e : expr_node -> ty -> expr
val mk_ee : eexpr_node -> ety -> eexpr

val e_export : expr -> eexpr

module Se : Set.S with type elt = expr
module He : Hashtbl.S with type key = expr
module Me : Map.S with type key = expr

(* ----------------------------------------------------------------------- *)
(** {2 Indicator functions} *)

val is_V : 'a gexpr -> bool
val is_H : 'a gexpr -> bool
val is_Tuple : 'a gexpr -> bool
val is_Proj : 'a gexpr -> bool
val is_some_Cnst : 'a gexpr -> bool
val is_Cnst : cnst -> 'a gexpr -> bool
val is_True : 'a gexpr -> bool
val is_False : 'a gexpr -> bool
val is_GGen : 'a gexpr -> bool
val is_GTGen : 'a gexpr -> bool
val is_some_App : 'a gexpr -> bool
val is_App : op -> 'a gexpr -> bool
val is_some_Nary : 'a gexpr -> bool
val is_Nary : naryop -> 'a gexpr -> bool
val is_ElemH : 'a gexpr -> bool
val is_GLog : 'a gexpr -> bool
val is_GTLog : 'a gexpr -> bool

(* ----------------------------------------------------------------------- *)
(** {3 Destructor functions} *)

exception Destr_failure of string

val destr_V      : 'a gexpr -> 'a Vsym.gt
val destr_H      : 'a gexpr -> 'a Hsym.gt * 'a gexpr
val destr_Tuple  : 'a gexpr -> 'a gexpr list
val destr_Proj   : 'a gexpr -> int * 'a gexpr
val destr_Cnst   : 'a gexpr -> cnst
val destr_App    : 'a gexpr -> op * 'a gexpr list
val destr_GMult  : 'a gexpr -> 'a gexpr * 'a gexpr
val destr_GExp   : 'a gexpr -> 'a gexpr * 'a gexpr
val destr_GLog   : 'a gexpr -> 'a gexpr
val destr_GTMult : 'a gexpr -> 'a gexpr * 'a gexpr
val destr_GTExp  : 'a gexpr -> 'a gexpr * 'a gexpr
val destr_GTLog  : 'a gexpr -> 'a gexpr
val destr_FOpp   : 'a gexpr -> 'a gexpr
val destr_FMinus : 'a gexpr -> 'a gexpr * 'a gexpr
val destr_FInv   : 'a gexpr -> 'a gexpr
val destr_FDiv   : 'a gexpr -> 'a gexpr * 'a gexpr
val destr_Eq     : 'a gexpr -> 'a gexpr * 'a gexpr
val destr_Not    : 'a gexpr -> 'a gexpr
val destr_Ifte   : 'a gexpr -> 'a gexpr * 'a gexpr * 'a gexpr
val destr_FPlus  : 'a gexpr -> 'a gexpr list
val destr_FMult  : 'a gexpr -> 'a gexpr list
val destr_Xor    : 'a gexpr -> 'a gexpr list
val destr_Land   : 'a gexpr -> 'a gexpr list

(* ----------------------------------------------------------------------- *)
(** {4 Constructor functions} *)

exception TypeError of (ty *  ty * expr * expr option * string)

val mk_V      : Vsym.t -> expr
val mk_H      : Hsym.t -> expr -> expr
val mk_Tuple  : expr list -> expr
val mk_Proj   : int -> expr -> expr
val mk_ElemH  : expr -> Hsym.t -> expr
val mk_GGen   : expr
val mk_GTGen  : expr
val mk_FZ     : expr
val mk_FOne   : expr
val mk_Z      : Lenvar.id -> expr
val mk_B      : bool -> expr
val mk_True   : expr
val mk_False  : expr
val mk_GMult  : expr -> expr -> expr
val mk_GExp   : expr -> expr -> expr
val mk_GLog   : expr -> expr
val mk_EMap   : expr -> expr -> expr
val mk_GTMult : expr -> expr -> expr
val mk_GTExp  : expr -> expr -> expr
val mk_GTLog  : expr -> expr
val mk_FOpp   : expr -> expr
val mk_FMinus : expr -> expr -> expr
val mk_FInv   : expr -> expr
val mk_FDiv   : expr -> expr -> expr
val mk_Eq     : expr -> expr -> expr
val mk_Not    : expr -> expr
val mk_Ifte   : expr -> expr -> expr -> expr
val mk_FPlus  : expr list -> expr
val mk_FMult  : expr list -> expr
val mk_Xor    : expr list -> expr
val mk_Land   : expr list -> expr

(** Constructors for exported expressions *)
module EConstructors :
  sig
    type t = IdType.exported
    exception TypeError of
                (ety * ety * eexpr * eexpr option * string)
    val ensure_ty_equal :
      ety -> ety -> eexpr -> eexpr option -> string -> unit
    val mk_V      : Vsym.et -> eexpr
    val mk_H      : Hsym.et -> eexpr -> eexpr
    val mk_Tuple  : eexpr list -> eexpr
    val mk_Proj   : int -> eexpr -> eexpr
    val mk_ElemH  : eexpr -> Hsym.et -> eexpr
    val mk_GGen   : eexpr
    val mk_GTGen  : eexpr
    val mk_FZ     : eexpr
    val mk_FOne   : eexpr
    val mk_Z      : t Type.Lenvar.gid -> eexpr
    val mk_B      : bool -> eexpr
    val mk_True   : eexpr
    val mk_False  : eexpr
    val mk_GMult  : eexpr -> eexpr -> eexpr
    val mk_GExp   : eexpr -> eexpr -> eexpr
    val mk_GLog   : eexpr -> eexpr
    val mk_EMap   : eexpr -> eexpr -> eexpr
    val mk_GTMult : eexpr -> eexpr -> eexpr
    val mk_GTExp  : eexpr -> eexpr -> eexpr
    val mk_GTLog  : eexpr -> eexpr
    val mk_FOpp   : eexpr -> eexpr
    val mk_FMinus : eexpr -> eexpr -> eexpr
    val mk_FInv   : eexpr -> eexpr
    val mk_FDiv   : eexpr -> eexpr -> eexpr
    val mk_Eq     : eexpr -> eexpr -> eexpr
    val mk_Not    : eexpr -> eexpr
    val mk_Ifte   : eexpr -> eexpr -> eexpr -> eexpr
    val mk_FPlus  : eexpr list -> eexpr
    val mk_FMult  : eexpr list -> eexpr
    val mk_Xor    : eexpr list -> eexpr
    val mk_Land   : eexpr list -> eexpr
  end

(* ----------------------------------------------------------------------- *)
(** {5 Pretty printing} *)
val pp_cnst : formatter -> cnst -> 'a Type.gty -> unit
val pp_exp  : formatter -> 'a gexpr -> unit
val pp_op   : formatter -> op -> 'a gexpr list -> unit
val pp_nop  : formatter -> naryop * 'a gexpr list -> unit

(* ----------------------------------------------------------------------- *)
(** {6 Generic functions on [expr]} *)

(** [e_sub_map f e] non-recursively applies [f] to all direct sub-expressions of [e], e.g.,
     if [e=Xor(a,b)] the a new term [Xor(f a, f b)] is returned.
     [e_sub_map] saves hashcons calls by detecting when [f] returns
     its argument unchanged.
     [e_sub_map] raises an exception if [f] changes the type. *)
val e_sub_map : (expr -> expr) -> expr -> expr

(** [e_fold f acc e] applies [f] to all direct sub-expressions of [e], e.g.,
    the results for [e=Xor(a,b)] is [f (f acc a) b]. *)
val e_sub_fold : ('a -> 'b gexpr -> 'a) -> 'a -> 'b gexpr -> 'a

(** [e_sub_iter f e] executes [f] for all direct sub-expressions of [e]
     for [f]s side-effects. *)
val e_sub_iter : ('a gexpr -> unit) -> 'a gexpr -> unit

(** [e_iter f e] executes [f] for all sub-expressions of [e] (including e)
     for [f]s side-effects. *)
val e_iter : ('a gexpr -> 'b) -> 'a gexpr -> unit

(** [e_exists p e] returns [true] if there is a subterms of [e] (including
     [e] itself) that satisfies [p]. *)
val e_exists : ('a gexpr -> bool) -> 'a gexpr -> bool

(** [e_forall p e] returns [true] if all subterms of [e]
    (including [e] itself satisfy [p]. *)
val e_forall : ('a gexpr -> bool) -> 'a gexpr -> bool

(** [e_find p e] return the first [e'] that is a subterm of [e] and satisfies [p].
     If there is no such [e'], then {!Not_found} is raised *)
val e_find : ('a gexpr -> bool) -> 'a gexpr -> 'a gexpr

(** [e_find_all p e] returns the the set of all [e'] that are subterms
     of [e] and satisfy [p]. *)
val e_find_all : (expr -> bool) -> expr -> Se.t

val e_vars : expr -> Se.t

(** [e_map f e] applies [f] recursively to all subterms of [e] proceeding
     in a bottom-up fashion. *)
val e_map : (expr -> expr) -> expr -> expr

(** [e_map_top f e] applies [f] recursively to all subterms of [e] proceeding
     in a top-down fashion. If [f] raises {!Not_found}, then [e_map_top]
     proceeds by applying [f] to the direct sub-expressions of the given
     expression. Otherwise, it returns without applying [f] to the subexpressions.  *)
val e_map_top : (expr -> expr) -> expr -> expr

(** [e_replace e1 e2 e] replaces all occurences of [e1] in [e] with [e2] *)
val e_replace : expr -> expr -> expr -> expr

(** [e_subst s e] replaces all occurences (in [e]) of elements [e1]
    in [dom(s)] with [s(e1)]. *)
val e_subst : expr Me.t -> expr -> expr

(** [e_vars e] returns the set of all variables in [e]. *)
val e_vars : expr -> Se.t

type ctxt = Vsym.t * expr
val inst_ctxt : ctxt -> expr -> expr

val typeError_to_string :
  'a gty * 'a gty * 'a gexpr * 'a gexpr option * string -> string

val catch_TypeError : (unit -> 'a) -> 'a