(*s Symbols in game definitions *)

(*i*)
open Abbrevs
open Util
open Type
(*i*)

module Asym = struct
  type t = { 
    id : Id.id;
    dom : ty;
    codom : ty;
  }

  type tt = t

  let hash asym = Id.hash asym.id 
  let equal : t -> t -> bool = (==)
  let compare (x : t) (y : t) = hash x - hash y

  module As = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = As.M
  module S = As.S
  module H = As.H

  let mk name dom codom = 
    { id = Id.mk name; dom = dom; codom = codom }

  let pp fmt os = F.fprintf fmt "%s" (Id.name os.id)
  let to_string os = Id.name os.id
end

module Osym = struct
  type t = { 
    id    : Id.id;
    dom   : ty;
    codom : ty;
  }

  type tt = t

  let hash os = Id.hash os.id 
  let equal : t -> t -> bool = (==)
  let compare (x : t) (y : t) = hash x - hash y

  module Os = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = Os.M
  module S = Os.S
  module H = Os.H

  let mk name dom codom = 
    { id = Id.mk name; dom = dom; codom = codom }

  let pp fmt os = F.fprintf fmt "%s" (Id.name os.id)
  let to_string os = Id.name os.id
end
