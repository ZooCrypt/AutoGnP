open Type
open IdType
open Util

type 'a gt = { 
  id    : 'a Id.gid;
  ro    : bool;          (* true if random oracle *)
  dom   : 'a gty;
  codom : 'a gty;
}

type t = internal gt

type et = exported gt

let export hs = {
  id = Id.export hs.id;
  ro = hs.ro;
  dom = ty_export hs.dom;
  codom = ty_export hs.codom
}

let hash hs = Id.hash hs.id 
let equal hs1 hs2 = Id.equal hs1.id hs2.id

module Hs = StructMake (struct
  type t = internal gt
  let tag = hash
end) 

module M = Hs.M
module S = Hs.S
module H = Hs.H

let mk name ro dom codom =
  { id = Id.mk name; ro; dom; codom }

let mke name i ro dom codom = 
  { id = Id.mke name i; ro; dom; codom}

let pp fmt hs = F.fprintf fmt "%s" (Id.name hs.id)
let tostring hs = Id.name hs.id

let is_ro hs = hs.ro
