(** Type for exported and internal (abstract) identifiers. *)

open Util

(*  Note: This should be an [mli], but then we get a linking
    error. *)

(** {!exported} is used as phantom type for [ID.gid] denoting exported
  identifiers where the tag may not be internal. *)
type exported

(** {!internal} is used as phantom type for [ID.gid] denoting identifiers where the tag is internal.
    {!internal} is a subtype of exported and we can coerce values (see {!export}) *)
type internal = private exported

module type ID = sig
  (** {!gid}s consist of a name and a tag and can be {!internal} or {!exported}. *)
  type 'a gid

  (** Returns the name. *)
  val name : 'a gid -> string

  (** Returns the tag. *)
  val tag : 'a gid -> int

  (** Pretty printer for {!gid}. *)
  val pp : F.formatter -> 'a gid -> unit

  (** internal identifiers. *)
  type id = internal gid

  (** {!equal} uses physical equality. *)
  val equal : id -> id -> bool

  (** The {!hash} function is injective. *)
  val hash : id -> int

  (** Uses the {!hash} function. *)
  val compare : id -> id -> int

  (** Create a new {!id} with the given name, the assigned tag is guaranteed
      to be unique (in a program run). *)
  val mk : string -> id

  module M : Map.S with type key = id
  module S : Set.S with type elt = id
  module H : Hashtbl.S  with type key = id

  (** exported identifiers. *)
  type eid = exported gid

  (** Create a new {!eid} with the given name and tag. *)
  val mke : string -> int -> eid

  (** Export {!id} (this is the identity function). *)
  val export : id -> eid
end
