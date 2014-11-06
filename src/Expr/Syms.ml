(*s Symbols for variables and other objects. *)

(*i*)
open Abbrevs
open Util
open Id
open Type
(*i*)

module Vsym = struct
  type t = { 
    id  : id;
    ty : ty;
  }

  type tt = t

  let hash ps = Id.hash ps.id
  let equal : t -> t -> bool = (==)
  let compare (x : t) (y : t) = hash x - hash y

  module Ps = StructMake (struct
    type t = tt
    let tag = hash
  end)

  module M = Ps.M
  module S = Ps.S
  module H = Ps.H

  let mk name ty = { id = Id.mk name; ty = ty; }

  let pp fmt ps = F.fprintf fmt "%s" (Id.name ps.id)
  let to_string ps = Id.name ps.id
  let set_of_list l =
    L.fold_right
      (fun vs acc -> S.add vs acc)
      l
      S.empty
end

module Hsym = struct
  type t = { 
    id    : Id.id;
    ro    : bool;          (*r true if random oracle *)
    dom   : ty;
    codom : ty;
  }

  type tt = t

  let hash hs = Id.hash hs.id 
  let equal hs1 hs2 = Id.equal hs1.id hs2.id

  module Hs = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = Hs.M
  module S = Hs.S
  module H = Hs.H

  let mk name ro dom codom =
    { id = Id.mk name; ro; dom; codom }

  let pp fmt hs = F.fprintf fmt "%s" (Id.name hs.id)
  let to_string hs = Id.name hs.id

  let is_ro hs = hs.ro
end

module Esym = struct
  type t = { 
    id : Id.id;
    source1 : Groupvar.id;
    source2 : Groupvar.id;
    target  : Groupvar.id;
  }

  type tt = t

  let hash es = Id.hash es.id 
  let equal es1 es2 = Id.equal es1.id es2.id

  module Es = StructMake (struct
    type t = tt
    let tag = hash
  end) 

  module M = Es.M
  module S = Es.S
  module H = Es.H

  let mk name source1 source2 target =
    { id = Id.mk name; source1 = source1;
      source2 = source2; target = target }

  let pp fmt hs = F.fprintf fmt "%s" (Id.name hs.id)

  let name hs = Id.name hs.id
end
