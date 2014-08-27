open Type
open IdType
open Util

type 'a gt = { 
  id : 'a Id.gid;
  source1 : 'a Groupvar.gid;
  source2 : 'a Groupvar.gid;
  target  : 'a Groupvar.gid;
}

type t = internal gt

type et = exported gt

let export es = {
  id = Id.export es.id;
  source1 = Groupvar.export es.source1;
  source2 = Groupvar.export es.source2;
  target  = Groupvar.export es.target;
}

let hash es = Id.hash es.id 
let equal es1 es2 = Id.equal es1.id es2.id

module Es = StructMake (struct
  type t = internal gt
  let tag = hash
end) 

module M = Es.M
module S = Es.S
module H = Es.H

let mk name source1 source2 target =
  { id = Id.mk name; source1 = source1;
    source2 = source2; target = target }

let mke name i source1 source2 target = 
  { id = Id.mke name i; source1 = source1;
    source2 = source2; target = target }

let pp fmt hs = F.fprintf fmt "%s" (Id.name hs.id)

let name hs =  (Id.name hs.id)
