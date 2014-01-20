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

let export os = {
  id = Id.export os.id;
  dom = ty_export os.dom;
  codom = ty_export os.codom
}

let hash os = Id.hash os.id 
let equal : t -> t -> bool = (==)
let compare (x : t) (y : t) = hash x - hash y

module Os = StructMake (struct
  type t = internal gt
  let tag = hash
end) 

module M = Os.M
module S = Os.S
module H = Os.H

let mk name dom codom = 
  { id = Id.mk name; dom = dom; codom = codom }

let mke name i dom codom = 
  { id = Id.mke name i; dom = dom; codom = codom }

(* let pp fmt os = Id.pp fmt os.id *)
(* FIXME: implememt renaming *)
let pp fmt os = Format.fprintf fmt "%s" (Id.name os.id)
let tostring os = Id.name os.id
