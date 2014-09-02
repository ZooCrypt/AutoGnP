(*s Symbols in game definitions *)

(*i*)
open Type
open Util
(*i*)

module Asym : sig
  type t = private { id : Id.id; dom : ty; codom : ty;}

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> ty -> ty -> t
  val pp : F.formatter -> t -> unit
  val to_string : t -> string
  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end

module Osym : sig
  type t = private { id : Id.id; dom : ty; codom : ty;}

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> ty -> ty -> t
  val pp : F.formatter -> t -> unit
  val to_string : t -> string
  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end
