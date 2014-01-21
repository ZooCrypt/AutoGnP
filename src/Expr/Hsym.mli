(** Hash function symbols. *)
open Type
open IdType

type 'a gt = private { 
  id    : 'a Id.gid; 
  ro    : bool;   (* true is random oracle *) 
  dom   : 'a gty;
  codom : 'a gty;
}

type t = internal gt
type et = exported gt
val export : t -> et
val hash : t -> int
val equal : t -> t -> bool
val mk : string -> bool -> ty -> ty -> t
val mke : string -> int -> bool -> ety -> ety -> et
val pp : Format.formatter -> 'a gt -> unit
val tostring : 'a gt -> string
val is_ro : 'a gt -> bool


module M : Map.S with type key = t
module S : Set.S with type elt = t
module H : Hashtbl.S with type key = t
