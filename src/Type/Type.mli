(** Types: {!ty} is hashconsed and contains internal {!id}s while {!ety} is not
    hashconsed and contains exported {!eid}s. *)

(* length variables for bitstrings *)
module Lenvar : IdType.ID

type 'a gty = { ty_node : 'a gty_node; ty_tag : int; }
and 'a gty_node =
    BS of 'a Lenvar.gid
  | Bool
  | G
  | GT
  | Fq
  | Prod of 'a gty list

(** The interface ensures that all values of
     type {!ty} are hashconsed *)
type ty = IdType.internal gty

val ty_equal : ty -> ty -> bool
val ty_hash : 'a gty -> int

module Hsty : Hashcons.S with type t = ty

module Mty : Map.S with type key = ty
module Sty : Set.S with type elt = ty
module Hty : Hashtbl.S with type key = ty

val mk_ty : IdType.internal gty_node -> Hsty.t

val mk_BS : Lenvar.id -> ty
val mk_G : ty
val mk_GT : ty
val mk_Fq : ty
val mk_Bool : ty
val mk_Prod : ty list -> ty

(** The interface ensures that all values of type {!ety} have tag [-1],
    i.e., structural equality ignores the tag. *)
type ety = IdType.exported gty

val mk_ety : IdType.exported gty_node -> ety

val ty_export : ty -> ety

val pp_ty : Format.formatter -> 'a gty -> unit
