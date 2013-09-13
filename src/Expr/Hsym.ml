open Type
open IdType
open Util

type 'a gt = { 
  id : 'a Id.gid;
  dom : 'a gty;
  codom : 'a gty;
}

type t = internal gt

type et = exported gt

let export hs = {
  id = Id.export hs.id;
  dom = ty_export hs.dom;
  codom = ty_export hs.codom
}

let hash hs = Id.hash hs.id 
let equal : t -> t -> bool = (==)
let compare (x : t) (y : t) = hash x - hash y

module Hs = StructMake (struct
  type t = internal gt
  let tag = hash
end) 

module M = Hs.M
module S = Hs.S
module H = Hs.H

let mk name dom codom = 
  { id = Id.mk name; dom = dom; codom = codom }

let mke name i dom codom = 
  { id = Id.mke name i; dom = dom; codom = codom }

let pp fmt hs = Id.pp fmt hs.id