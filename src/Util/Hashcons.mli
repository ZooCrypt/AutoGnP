(** Hash-consing registers all values of a given type in a hashtable.
    If all values of the type are obtained using {!S.hashcons} then this
    guarantees that structural equality implies physical equality.
    Additionally, the hash table maintains unique integer [tag]s
    for each value of the type that can be used for [Map]s, [Set]s,
    and [Hashtbl]s. *)

(** We can hashcons values for which the {!HashedType} interface is implemented *)
module type HashedType =
  sig
    type t
    val equal : t -> t -> bool
      (** Equality function used type *)

    val hash : t -> int
      (** Return [int] hash of value used for hashtable storage and retrieval.
          Can be noninjective which degrades performance (collisions in hashtable). *)
  
    val tag : int -> t -> t
      (** Function to assign tags to values. Usually, t is a record with an [int] field.
          The tag is unrelated to the hash and usually depends on the content of the hash
          table. *)
  end

(** The hashcons interface. *)
module type S =
  sig
    type t
    val hashcons : t -> t
      (** Register value in hashtable and set tag. *)

    val iter : (t -> unit) -> unit
      (** Iterate over entries of hash table. *)

(*    val stats : unit -> int * int * int * int * int * int
      (** Retrieve hashtable stats. *)
    val clear : unit -> unit
      (** Remove all entries from hashtable. *) *)
  end

(** Make hashcons module for {!HashedType}. *)
module Make : functor (H : HashedType) -> S with type t = H.t

(** Combine two integers for hash. *)
val combine : int -> int -> int

(** Combine three integers for hash. *)
val combine2 : int -> int -> int -> int

(** Combine list of integers for hash. *)
val combine_list : ('a -> int) -> int -> 'a list -> int
