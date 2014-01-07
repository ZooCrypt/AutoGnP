(** Bilinear map function symbols. *)
open Type
open IdType

type 'a gt = private { id : 'a Id.gid;
                       source1 : 'a Groupvar.gid;
                       source2 : 'a Groupvar.gid;
                       target : 'a Groupvar.gid; }
type t = internal gt
type et = exported gt
val export : t -> et
val hash : t -> int
val equal : t -> t -> bool
val mk : string -> Groupvar.id -> Groupvar.id -> Groupvar.id -> t
val mke : string -> int -> Groupvar.eid -> Groupvar.eid -> Groupvar.eid -> et
val pp : Format.formatter -> 'a gt -> unit
module M : Map.S with type key = t
module S : Set.S with type elt = t
module H : Hashtbl.S with type key = t