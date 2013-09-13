(** Types: {!ty} is hashconsed and contains internal {!id}s while {!ety} is not
    hashconsed and contains exported {!eid}s. *)
module Tyvar : IdType.ID

type 'a gty = private { ty_sum : ('a Tyvar.gid) list; ty_tag : int }

val pp_ty : Format.formatter -> 'a gty -> unit

(* ----------------------------------------------------------------------- *)

(** The interface ensures that all values of type {!ty} are hashconsed *)
type ty = IdType.internal gty

val ty_equal : ty -> ty -> bool
val ty_hash : ty -> int

module Hsty : Hashcons.S with type t = ty

module Mty : Map.S with type key = ty
module Sty : Set.S with type elt = ty
module Hty : Hashtbl.S with type key = ty

val mk_ty : Tyvar.id list -> ty

(** [is_ty_var ty] returns [true] if [ty] is just a type variable,
    i.e., not a sum. *)
val is_ty_var : 'a gty -> bool

(** [is_ty_zero ty] returns [true] if [ty] is zero,
    i.e., the empty sum. *)
val is_ty_zero : 'a gty -> bool

(** [ty_minus ty1 ty2] returns [Some(ty3)] if there is [ty3] such
    that [ty1 = ty2 + ty3] and [None] otherwise. *)
val ty_minus : ty -> ty -> ty option

(** [ty_concat ty1 ty2] concatenates [ty1] and [ty2]. A hashtable is used
    for memoization. *)
val ty_concat : ty -> ty -> ty

(** [ty_concat_l l] concatenates the types in [l]. *)
val ty_concat_l : ty list -> ty

(* ----------------------------------------------------------------------- *)

(** The interface ensures that all values of type {!ety} have tag [-1],
    i.e., structural equality ignores the tag. *)
type ety = IdType.exported gty

val ty_export : ty -> ety

val mk_ety : Tyvar.eid list -> ety