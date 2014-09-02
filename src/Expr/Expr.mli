(*s Typed algebraic expression: We distinguish
    internal/hashconsed and exported expressions. *)

(*i*)
open Type
open Util
open Syms
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Expressions} *)

type proj_type = Type.ty * Type.ty * Type.ty

type cnst =
    GGen
  | FNat of int
  | Z
  | B of bool

val cnst_hash : cnst -> int

type op =
    GExp of Groupvar.id
  | GLog of Groupvar.id
  | FOpp
  | FMinus
  | FInv
  | FDiv
  | Eq
  | Not
  | Ifte
  | EMap of Esym.t

val op_hash : op -> int

type nop =
    FPlus
  | FMult
  | Xor
  | Land
  | GMult

val nop_hash : nop -> int

type expr = { e_node : expr_node; e_ty : Type.ty; e_tag : int; }
and expr_node =
    V of Vsym.t
  | H of Hsym.t * expr
  | Tuple of expr list
  | Proj of int * expr
  | Cnst of cnst
  | App of op * expr list
  | Nary of nop * expr list
  | Exists of expr * expr * (Vsym.t * Hsym.t) list

val e_equal : expr -> expr -> bool
val e_hash : expr -> int
val e_compare : expr -> expr -> int

module Hse : Hashcons.S with type t = expr

val mk_e : expr_node -> ty -> expr

module Se : Set.S with type elt = expr
module He : Hashtbl.S with type key = expr
module Me : Map.S with type key = expr

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Indicator functions} *)

val is_V : expr -> bool
val is_H : expr -> bool
val is_Tuple : expr -> bool
val is_Proj : expr -> bool
val is_some_Cnst : expr -> bool
val is_Cnst : cnst -> expr -> bool
val is_FNat : expr -> bool
val is_FOne : expr -> bool
val is_FZ : expr -> bool
val is_True : expr -> bool
val is_False : expr -> bool
val is_GGen : expr -> bool
val is_GLog : expr -> bool
val is_some_App : expr -> bool
val is_App : op -> expr -> bool
val is_FDiv : expr -> bool
val is_FOpp : expr -> bool
val is_some_Nary : expr -> bool
val is_Nary : nop -> expr -> bool
val is_FPlus : expr -> bool
val is_FMult : expr -> bool
val is_Xor : expr -> bool  
val is_Exists : expr -> bool
val is_Eq    : expr -> bool
val is_field_op : op -> bool
val is_field_nop : nop -> bool
val is_field_exp : expr -> bool
val is_Land : expr -> bool

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Destructor functions} *)

exception Destr_failure of string

val destr_V      : expr -> Vsym.t
val destr_H      : expr -> Hsym.t * expr
val destr_Tuple  : expr -> expr list
val destr_Proj   : expr -> int * expr
val destr_Cnst   : expr -> cnst
val destr_FNat   : expr -> int
val destr_App    : expr -> op * expr list
val destr_GMult  : expr -> (expr) list
val destr_GExp   : expr -> expr * expr
val destr_GLog   : expr -> expr
val destr_EMap   : expr -> Esym.t * expr * expr
val destr_FOpp   : expr -> expr
val destr_FMinus : expr -> expr * expr
val destr_FInv   : expr -> expr
val destr_FDiv   : expr -> expr * expr
val destr_Eq     : expr -> expr * expr
val destr_Not    : expr -> expr
val destr_Ifte   : expr -> expr * expr * expr
val destr_FPlus  : expr -> expr list
val destr_FMult  : expr -> expr list
val destr_Xor    : expr -> expr list
val destr_Land   : expr -> expr list
val destruct_Land : expr -> expr list
val destr_Exists  : expr -> expr * expr * (Vsym.t * Hsym.t) list

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Constructor functions} *)

exception TypeError of (ty *  ty * expr * expr option * string)

val mk_V      : Vsym.t -> expr
val mk_H      : Hsym.t -> expr -> expr
val mk_Tuple  : expr list -> expr
val mk_Proj   : int -> expr -> expr
val mk_Exists : expr -> expr -> (Vsym.t * Hsym.t) list -> expr
val mk_GGen   : Groupvar.id -> expr
val mk_FNat   : int -> expr
val mk_FOne   : expr
val mk_FZ     : expr
val mk_Z      : Lenvar.id -> expr
val mk_B      : bool -> expr
val mk_True   : expr
val mk_False  : expr
val mk_GMult  : expr list -> expr
val mk_GExp   : expr -> expr -> expr
val mk_GLog   : expr -> expr
val mk_EMap   : Esym.t -> expr -> expr -> expr
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

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Pretty printing} *)

val pp_cnst : F.formatter -> cnst -> Type.ty -> unit
val pp_exp  : F.formatter -> expr -> unit
val pp_op   : F.formatter -> op * expr list -> unit
val pp_nop  : F.formatter -> nop * expr list -> unit

val pp_exp_tnp  : F.formatter -> expr -> unit

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Generic functions on [expr]} *)

(** [e_sub_map f e] non-recursively applies [f] to all direct sub-expressions of [e], e.g.,
    if [e=Xor(a,b)] then a new term [Xor(f a, f b)] is returned.
    [e_sub_map] saves hashcons calls by detecting when [f] returns
    its argument unchanged.
    [e_sub_map] raises an exception if [f] changes the type. *)
val e_sub_map : (expr -> expr) -> expr -> expr

(** [e_fold f acc e] applies [f] to all direct sub-expressions of [e], e.g.,
    the results for [e=Xor(a,b)] is [f (f acc a) b]. *)
val e_sub_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a

(** [e_sub_iter f e] executes [f] for all direct sub-expressions of [e]
    for [f] s side-effects. *)
val e_sub_iter : (expr -> unit) -> expr -> unit

(** [e_iter f e] executes [f] for all sub-expressions of [e] (including e)
    for [f] s side-effects. *)
val e_iter : (expr -> 'b) -> expr -> unit

(** [e_exists p e] returns [true] if there is a subterms of [e] (including
    [e] itself) that satisfies [p]. *)
val e_exists : (expr -> bool) -> expr -> bool

(** [e_forall p e] returns [true] if all subterms of [e]
    (including [e] itself) satisfy [p]. *)
val e_forall : (expr -> bool) -> expr -> bool

(** [e_find p e] return the first [e'] that is a subterm of [e] and satisfies [p].
    If there is no such [e'], then [Not_found] is raised *)
val e_find : (expr -> bool) -> expr -> expr

(** [e_find_all p e] returns the the set of all [e'] that are subterms
    of [e] and satisfy [p]. *)
val e_find_all : (expr -> bool) -> expr -> Se.t

(** [e_map f e] applies [f] recursively to all subterms of [e] proceeding
    in a bottom-up fashion. *)
val e_map : (expr -> expr) -> expr -> expr

(** [e_ty_outermost ty e] returns the list of outmost subterms of [e] of
    type [ty] *)
val e_ty_outermost : ty -> expr -> expr list


(** [e_map_top f e] applies [f] recursively to all subterms of [e] proceeding
    in a top-down fashion. If [f] raises [Not_found], then [e_map_top]
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

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Useful functions on [expr]} *)

val se_of_list : expr list -> Se.t

val has_log : expr -> bool

val is_ppt : expr -> bool

type ctxt = Vsym.t * expr

val inst_ctxt : ctxt -> expr -> expr

(** [sub t] is a generic subtraction function that
    returns context [(x1,x2,c)] and a [zero]
    such that forall e1 e2:t, [inst_ctxt c e1 e2] =E [e1 - e2]
    and [inst_ctxt c e2 e2] = [zero]. *)
val sub : ty -> (Vsym.t * ctxt) * expr

val is_Zero : expr -> bool
val mk_Zero   : ty -> expr

val typeError_to_string : ty * ty * expr * expr option * string -> string

val catch_TypeError : (unit -> 'a) -> 'a
