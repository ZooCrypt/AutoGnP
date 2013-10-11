(** Oracle symbols. *)
open Type
open IdType

type 'a gt = private { id : 'a Id.gid; dom : 'a gty; codom : 'a gty;}
type t = internal gt
type et = exported gt
val export : t -> et
val hash : t -> int
val equal : t -> t -> bool
val compare : t -> t -> int
val mk : string -> ty -> ty -> t
val mke : string -> int -> ety -> ety -> et
val pp : Format.formatter -> 'a gt -> unit
module M : Map.S with type key = t
module S : Set.S with type elt = t
module H : Hashtbl.S with type key = t