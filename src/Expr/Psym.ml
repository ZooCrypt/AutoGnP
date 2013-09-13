open Type
open IdType
open Util

type 'a gt = { 
  id  : 'a Id.gid;
  dom : 'a gty;
}

type t = internal gt

type et = exported gt

let export ps = {id = Id.export ps.id; dom = ty_export ps.dom}

let hash ps = Id.hash ps.id 
let equal : t -> t -> bool = (==)
let compare (x : t) (y : t) = hash x - hash y

module Ps = StructMake (struct
  type t = internal gt
  let tag = hash
end) 

module M = Ps.M
module S = Ps.S
module H = Ps.H

let mk name dom = { id = Id.mk name; dom = dom; }

let mke name i dom = { id = Id.mke name i; dom = dom; }

let pp fmt ps = Id.pp fmt ps.id