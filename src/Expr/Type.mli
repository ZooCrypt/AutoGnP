(*s Hashconsed types *)

(*i*)
open Util
(*i*)

(** length variables for bitstrings *)
module Lenvar : IdType.ID

(** identifier for different groups *)
module Groupvar : IdType.ID

type ty = { ty_node : ty_node; ty_tag : int; }
and ty_node =
    BS of Lenvar.id
  | Bool
  | G of Groupvar.id
  | Fq
  | Prod of ty list
  | Int (* used during extraction *)

val ty_equal : ty -> ty -> bool
val ty_hash : ty -> int
val ty_compare : ty -> ty -> int

module Hsty : Hashcons.S with type t = ty

module Mty : Map.S with type key = ty
module Sty : Set.S with type elt = ty
module Hty : Hashtbl.S with type key = ty

val mk_ty : ty_node -> Hsty.t

val mk_BS : Lenvar.id -> ty
val mk_G : Groupvar.id -> ty
val mk_Fq : ty
val mk_Bool : ty
val mk_Prod : ty list -> ty
val mk_Int  : ty

val is_G : ty -> bool
val is_Fq : ty -> bool
val destr_G : ty -> Groupvar.id
val destr_BS : ty -> Lenvar.id
val destr_Prod : ty -> ty list

val pp_ty : F.formatter -> ty -> unit
