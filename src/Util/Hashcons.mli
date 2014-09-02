(*s Hash-consing registers all values of a given type in a hashtable.
    If all values of the type are obtained using {!S.hashcons} then this
    guarantees that structural equality implies physical equality.
    Additionally, the hash table maintains unique integer [tag]s
    for each value of the type that can be used for [Map]s, [Set]s,
    and [Hashtbl]s. *)

module type HashedType = HashconsTypes.HashedType

module type S = HashconsTypes.S

(** Make hashcons module for {!HashedType}. *)
module Make : functor (H : HashedType) -> S with type t = H.t

(** Combine two integers for hash. *)
val combine : int -> int -> int

(** Combine three integers for hash. *)
val combine2 : int -> int -> int -> int

(** Combine list of integers for hash. *)
val combine_list : ('a -> int) -> int -> 'a list -> int
