open Type
open IdType
open Util
open Id

type 'a gt = { 
  id  : 'a gid;
  ty : 'a gty;
}

type t = internal gt

type et = exported gt

let export ps = {id = Id.export ps.id; ty = ty_export ps.ty}

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

let mk name ty = { id = Id.mk name; ty = ty; }

let mke name i ty = { id = Id.mke name i; ty = ty; }

(* let pp fmt ps = Id.pp fmt ps.id *)
(* FIXME: implememt renaming *)
let pp fmt ps = Format.fprintf fmt "%s" (Id.name ps.id)
