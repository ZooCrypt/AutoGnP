(* * Symbols for variables and other objects *)

(* ** Imports *)
open Type
open Abbrevs
open Id

(* ** Oracle symbols
 * ----------------------------------------------------------------------- *)

module OrclSym : sig
  type t = private {
    id    : id;
    dom   : ty;
    codom : ty;
  }

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

(* ** Qualified symbols
 * ----------------------------------------------------------------------- *)

type 'a qual = Unqual | Qual of 'a
val map_qual : ('a -> 'b) -> 'a qual -> 'b qual

(* ** Variable symbols
 * ----------------------------------------------------------------------- *)

module VarSym : sig
  type t = private {
    id   : id;
    qual : OrclSym.t qual;
    ty : ty;
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> ty -> t
  val mk_qual : string -> OrclSym.t qual -> ty -> t
  val pp_qual : ?qual:OrclSym.t qual -> F.formatter -> t -> unit
  val pp : F.formatter -> t -> unit
  val to_string : t -> string

  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t

  val set_of_list : t list -> S.t
end

(* ** Adversary procedure symbols
 * ----------------------------------------------------------------------- *)

module AdvSym : sig
  type t = private {
    id  : id;
    dom : ty;
    codom : ty;
  }

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

(* ** Bilinear map symbols
 * ----------------------------------------------------------------------- *)

module EmapSym : sig
  type t = private {
    id      : id;
    source1 : Groupvar.id;
    source2 : Groupvar.id;
    target  : Groupvar.id;
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> Groupvar.id -> Groupvar.id -> Groupvar.id -> t
  val pp : F.formatter -> t -> unit
  val name : t -> string

  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end

(* ** Permutation symbols
 * ----------------------------------------------------------------------- *)

module PermSym : sig
  type t = private {
    id  : Permvar.id;
    dom : ty;
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> ty -> t
  val pp : F.formatter -> t -> unit
  val name : t -> string

  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end

(* ** Uninterpreted function symbols
 * ----------------------------------------------------------------------- *)

module FunSym : sig
  type t = private {
    id    : id;
    dom   : ty;
    codom : ty;
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> ty -> ty -> t
  val to_string : t -> string
  val pp : F.formatter -> t -> unit

  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end

(* ** Random Oracle Symbols
 * ----------------------------------------------------------------------- *)

module RoSym : sig
  type t = private {
    id    : id;
    dom   : ty;
    codom : ty;
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> ty -> ty -> t
  val to_string : t -> string
  val pp : F.formatter -> t -> unit

  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end


(* ** Map Symbols
 * ----------------------------------------------------------------------- *)

module MapSym : sig
  type t = private {
    id    : id;
    dom   : ty;
    codom : ty;
  }

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val mk : string -> ty -> ty -> t
  val to_string : t -> string
  val pp : F.formatter -> t -> unit

  module M : Map.S with type key = t
  module S : Set.S with type elt = t
  module H : Hashtbl.S with type key = t
end
