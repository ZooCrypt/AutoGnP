(* * Types (hashconsed) *)

(* ** Imports *)
open Abbrevs

(* ** Identifiers *)

(** length variables for bitstrings *)
module Lenvar : IdType.ID

(** identifier for different permutations *)
module Permvar : IdType.ID
        
(** identifier for different groups *)
module Groupvar : IdType.ID

(* ** Permutation keys *)

module KeyElem : sig
  type t = SKey | PKey

  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool
  val pp : F.formatter -> t -> unit
end

(* ** Types and type nodes *)

type ty = private { ty_node : ty_node; ty_tag : int; }
and ty_node =
  | BS of Lenvar.id
  | Bool
  | G of Groupvar.id
  | Fq
  | Prod of ty list
  | Int (* used during extraction *)
  | KeyPair of Permvar.id
  | KeyElem of KeyElem.t * Permvar.id
      
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
val mk_KeyPair : Permvar.id -> ty
val mk_KeyElem : KeyElem.t -> Permvar.id -> ty
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
val destr_KeyPair_exn : ty -> Permvar.id
val destr_KeyElem_exn : ty -> (KeyElem.t * Permvar.id)
val destr_Prod_exn    : ty -> ty list
val destr_Prod        : ty -> (ty list) option

(* ** Pretty printing *)

val pp_group : F.formatter -> Groupvar.id -> unit
val pp_ty    : F.formatter -> ty -> unit
