(* * Types (hashconsed) *)

(* ** Imports *)
open Abbrevs

(* ** Identifiers *)

(** length variables for bitstrings *)
module Lenvar : (module type of Id)

(** identifier for types *)
module Tysym : (module type of Id)

(** identifier for different permutations *)
module Permvar : (module type of Id)

(** identifier for different groups *)
module Groupvar : (module type of Id)

(* ** Types and type nodes *)

type ty = private { ty_node : ty_node; ty_tag : int; }
and ty_node =
  | BS of Lenvar.id
  | Bool
  | G of Groupvar.id
  | TySym of Tysym.id
  | Fq
  | Prod of ty list
  | Int (* used during extraction *)

val equal_ty   : ty -> ty -> bool
val hash_ty    : ty -> int
val compare_ty : ty -> ty -> int

module Hsty : Hashcons.S with type t = ty

module Mty : Map.S with type key = ty
module Sty : Set.S with type elt = ty
module Hty : Hashtbl.S with type key = ty

val mk_ty : ty_node -> Hsty.t

(* ** Constructor functions *)

val mk_BS      : Lenvar.id -> ty
val mk_G       : Groupvar.id -> ty
val mk_TySym   : Tysym.id -> ty
val mk_Fq      : ty
val mk_Bool    : ty
val mk_Prod    : ty list -> ty
val mk_Int     : ty

(* ** Indicator and destructor functions *)

val is_G	      : ty -> bool
val is_Fq	      : ty -> bool
val is_Prod	      : ty -> bool
val destr_G_exn	      : ty -> Groupvar.id
val destr_BS_exn      : ty -> Lenvar.id
val destr_Prod_exn    : ty -> ty list
val destr_Prod        : ty -> (ty list) option

(* ** Pretty printing *)

val pp_group : F.formatter -> Groupvar.id -> unit
val pp_ty    : F.formatter -> ty -> unit
