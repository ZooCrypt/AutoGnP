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
    lkup  : bool;   (*r true is LookUp call in random oracle *)
    dom   : ty;
    codom : ty;
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val mk : string -> ro:bool -> ?lkup:bool -> ty -> ty -> t
  val pp : F.formatter -> t -> unit
  val to_string : t -> string
  val is_ro : t -> bool
  val is_lkup : t -> bool


  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end

module Oracle : sig
  type t = private
    | RO of Hsym.t
    |  O of Osym.t

  val mk_RO : Hsym.t -> t
  val mk_O  : Osym.t -> t 

  val hash : t -> int
  val equal : t -> t -> bool
  val mk : string -> ro:bool -> ?lkup:bool -> ty -> ty -> t
  val pp : F.formatter -> t -> unit
  val to_string : t -> string
  val is_ro : t -> bool
  val is_lkup : t -> bool
  val get_id : t -> Id.id
  val get_dom : t -> ty
  val get_codom : t -> ty
  exception Destr_failure of string
  val destr_as_Osym_t : t -> Osym.t
  val destr_as_Hsym_t : t -> Hsym.t
                               

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
	    
