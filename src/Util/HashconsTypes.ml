(* * Module types for hash-consing. *)

(** We can hashcons values for which the {!HashedType} interface is implemented. *)
module type HashedType = sig
  type t

  (** Equality function used for type. *)
  val equal : t -> t -> bool

  (** Return [int] hash of value used for hashtable storage and retrieval.
      Can be noninjective which degrades performance (collisions in hashtable). *)
  val hash : t -> int

  (** Function to assign tags to values. Usually, t is a record with an [int] field.
      The tag is unrelated to the hash and usually depends on the content of the hash
      table. *)  
  val tag : int -> t -> t
end

(** The hashcons interface. *)
module type S = sig
  type t

  (** Register value in hashtable and set tag. *)
  val hashcons : t -> t
end
