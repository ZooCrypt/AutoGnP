(*s Symbols for variables and other objects. *)

(*i*)
open Type
open Abbrevs
(*i*)

module Asym : sig
  type t = private { id : Id.id; dom : ty; codom : ty;}

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> ty -> ty -> t
  val pp : F.formatter -> t -> unit
  val pp_long : F.formatter -> t -> unit
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
  val pp_long : F.formatter -> t -> unit
  val to_string : t -> string
  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end

type 'a qual = Unqual | Qual of 'a
val map_qual : ('a -> 'b) -> 'a qual -> 'b qual

module Vsym : sig
  type t = private { id : Id.id; qual : Osym.t qual; ty : ty; }

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> ty -> t
  val mk_qual : string -> Osym.t qual -> ty -> t
  val pp_qual : ?qual:Osym.t qual -> F.formatter -> t -> unit
  val pp : F.formatter -> t -> unit
  val to_string : t -> string

  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t

  val set_of_list : t list -> S.t
end

module Hsym : sig
  type t = private { 
    id    : Id.id; 
    ro    : bool;   (*r true is random oracle *) 
    dom   : ty;
    codom : ty;
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val mk : string -> bool -> ty -> ty -> t
  val pp : F.formatter -> t -> unit
  val to_string : t -> string
  val is_ro : t -> bool


  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end

module Esym : sig
  type t = private {
    id : Id.id;
    source1 : Groupvar.id;
    source2 : Groupvar.id;
    target : Groupvar.id; 
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val mk : string -> Groupvar.id -> Groupvar.id -> Groupvar.id -> t
  val pp : F.formatter -> t -> unit
  val name : t -> string

  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end

module Psym : sig
  type t = private { 
      id : Id.id;
      dom : ty;
      pid : Permvar.id;
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val mk : string -> ty -> Permvar.id -> t
  val pp : F.formatter -> t -> unit
  val name : t -> string

  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end
	    
