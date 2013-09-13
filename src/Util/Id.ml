open Util
open IdType

type 'a gid = {
  name_ : string;
  tag_ : int;
}

let name i = i.name_

let tag i = i.tag_

let pp fmt i =
  if i.tag_ = 0 then
    Format.fprintf fmt "%s" i.name_
  else
    Format.fprintf fmt "%s.%i" i.name_ i.tag_

(* ----------------------------------------------------------------------- *)

type id = internal gid

let equal : id -> id -> bool = (==)
let hash i = i.tag_
let compare x y = Pervasives.compare (hash x) (hash y)

let mk s = { name_ = s; tag_ = unique_int ()}

module SM = StructMake (struct
  type t = id
  let  tag i = i.tag_
end)

module M = SM.M
module S = SM.S
module H = SM.H

(* ----------------------------------------------------------------------- *)

type eid = exported gid

let mke s t = { name_ = s; tag_ = t }

let export id = (id :> eid)