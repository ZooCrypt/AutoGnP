(** Typed algebraic expression: We distinguish internal/hashconsed and external expressions.  *)

open IdType
open Type

(* ----------------------------------------------------------------------- *)
(** {1 Expressions} *)

type 'a proj_type = 'a gty * 'a gty * 'a gty

(** We only consider three fixed (non-random) variables in expressions *)
type var = Msg     (** the message [m_b] *)
         | Cipher  (** the cipher argument to the decryption query ([Ex c in L_D. ..]) *)
         | Star    (** the distinguished variable in a context *)

type 'a gexpr = private { e_node : 'a gexpr_node; e_ty : 'a Type.gty; e_tag : int; }
and 'a gexpr_node =
    Z
      (** the all zero bitstring *)
  | V    of var
      (** (non-random) variable *)
  | R    of 'a Rsym.gt
      (** random variable *)
  | P    of 'a Psym.gt   * 'a gexpr
      (** one-way permutation application *)
  | Pinv of 'a Psym.gt   * 'a gexpr
      (** one-way permutation application (inverse) *)
  | H    of 'a Hsym.gt   * 'a gexpr
      (** hash function application *)
  | App  of                'a gexpr list
      (** concatenation of bitstrings *)
  | Proj of 'a proj_type * 'a gexpr
      (** projection of bits from bitstring *)
  | Xor  of                'a gexpr * 'a gexpr
      (** Exclusive-or of bitstrings *)

type expr = internal gexpr
type expr_node = internal gexpr_node

type eexpr = exported gexpr
type eexpr_node = exported gexpr_node

val e_equal : expr -> expr -> bool
val e_hash : expr -> int
val e_compare : expr -> expr -> int

val mk_e : expr_node -> ty -> expr

val mk_ee : eexpr_node -> ety -> eexpr

module Hse : Hashcons.S with type t = expr

val e_export : expr -> eexpr

module Se : Set.S with type elt = expr
module He : Hashtbl.S with type key = expr
module Me : Map.S with type key = expr

(* ----------------------------------------------------------------------- *)
(** {2 Indicator functions} *)

val is_Z : 't gexpr -> bool
val is_V : 't gexpr -> bool
val is_Msg : 't gexpr -> bool
val is_Cipher : 't gexpr -> bool
val is_Star : 't gexpr -> bool
val is_R : 't gexpr -> bool
val is_P : 't gexpr -> bool
val is_Pinv : 't gexpr -> bool
val is_H : 't gexpr -> bool
val is_Xor : 't gexpr -> bool
val is_App : 't gexpr -> bool
val is_Proj : 't gexpr -> bool

(* ----------------------------------------------------------------------- *)
(** {3 Destructor functions} *)

exception Destr_failure of string
val destr_V : 'a gexpr -> var
val destr_P : 'a gexpr -> 'a Psym.gt * 'a gexpr
val destr_R : 'a gexpr -> 'a Rsym.gt
val destr_Pinv : 'a gexpr -> 'a Psym.gt * 'a gexpr
val destr_H : 'a gexpr -> 'a Hsym.gt * 'a gexpr
val destr_Xor : 'a gexpr -> 'a gexpr * 'a gexpr
val destr_App : 'a gexpr -> 'a gexpr list
val destr_Proj : 'a gexpr -> 'a proj_type * 'a gexpr

(* ----------------------------------------------------------------------- *)
(** {4 Constructor functions} *)

exception TypeError of (ty *  ty * expr * expr option * string)
val mk_Z : ty ->  expr
val mk_V : var -> ty ->  expr
val mk_Msg : ty ->  expr
val mk_Cipher : ty ->  expr
val mk_Star : ty ->  expr
val mk_R : Rsym.t ->  expr
val mk_P : Psym.t -> expr ->  expr
val mk_Pinv : Psym.t -> expr -> expr
val mk_H : Hsym.t -> expr ->  expr
val mk_App : expr list ->  expr
val mk_Proj : ty *  ty *  ty -> expr ->  expr
  (** Takes length of skip, take, and remainder. *)
val mk_Proj2 : ty *  ty -> expr ->  expr
  (** Computes length of remainder. *)
val mk_Xor : expr -> expr ->  expr

(** Constructors for exported expressions *)
module EConstructors :
sig
  type t = exported
  exception TypeError of (ety *  ety * eexpr * eexpr option * string)
  val mk_Z : ety ->  eexpr
  val mk_V : var -> ety ->  eexpr
  val mk_Msg : ety ->  eexpr
  val mk_Cipher : ety ->  eexpr
  val mk_Star : ety ->  eexpr
  val mk_R : Rsym.et -> eexpr
  val mk_P : Psym.et -> eexpr ->  eexpr
  val mk_Pinv : Psym.et -> eexpr -> eexpr
  val mk_H : Hsym.et -> eexpr ->  eexpr
  val mk_App : eexpr list ->  eexpr
  val mk_Proj : ety *  ety *  ety -> eexpr ->  eexpr
  val mk_Xor : eexpr -> eexpr ->  eexpr
end

(* ----------------------------------------------------------------------- *)
(** {5 Pretty printing} *)

val pp_var   : Format.formatter -> var -> unit
val pp_exp   : Format.formatter -> 't gexpr -> unit
val pp_b_exp : Format.formatter -> 't gexpr -> unit

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
val e_sub_fold : ('a -> 't gexpr -> 'a) -> 'a -> 't gexpr -> 'a

(** [e_sub_iter f e] executes [f] for all direct sub-expressions of [e]
     for [f]s side-effects. *)
val e_sub_iter : ('t gexpr -> unit) -> 't gexpr -> unit

(** [e_iter f e] executes [f] for all sub-expressions of [e] (including e)
     for [f]s side-effects. *)
val e_iter : ('t gexpr -> unit) -> 't gexpr -> unit

(** [e_exists p e] returns [true] if there is a subterms of [e] (including
     [e] itself) that satisfies [p]. *)
val e_exists : ('t gexpr -> bool) -> 't gexpr -> bool

(** [e_forall p e] returns [true] if all subterms of [e]
    (including [e] itself satisfy [p]. *)
val e_forall : ('t gexpr -> bool) -> 't gexpr -> bool

(** [e_find p e] return the first [e'] that is a subterm of [e] and satisfies [p].
     If there is no such [e'], then {!Not_found} is raised *)
val e_find : ('t gexpr -> bool) -> 't gexpr -> 't gexpr

(** [e_find_all p e] returns the the set of all [e'] that are subterms
     of [e] and satisfy [p]. *)
val e_find_all : (expr -> bool) -> expr -> Se.t

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

(** [e_rvars e] returns the set of all random variables in [e]. *)
val e_rvars : expr -> Se.t
