open Util
open IdType

module Lenvar : IdType.ID = Id

type 'a gty = {
  ty_node : 'a gty_node;
  ty_tag : int
}
and 'a gty_node =
  | BS   of ('a Lenvar.gid)
  | Bool
  | G
  | GT
  | Fq
  | Prod of ('a gty  list)

type ty = internal gty
type ety = exported gty

let ty_equal : ty -> ty -> bool = (==)

let ty_hash t = t.ty_tag

module Hsty = Hashcons.Make (struct
  type t = ty
  let equal t1 t2 = match t1.ty_node, t2.ty_node with
    | BS lv1, BS lv2     -> Lenvar.equal lv1 lv2
    | Bool, Bool         -> true
    | G, G               -> true
    | GT, GT             -> true
    | Fq, Fq             -> true
    | Prod ts1, Prod ts2 -> list_eq_for_all2 ty_equal ts1 ts2
    | _                  -> false
  let hash t = match t.ty_node with
    | BS lv   -> Lenvar.hash lv
    | Bool    -> 1
    | G       -> 2
    | GT      -> 3
    | Fq      -> 4
    | Prod ts -> Hashcons.combine_list ty_hash 3 ts
  let tag n t = { t with ty_tag = n }
end)

module Ty = StructMake (struct
  type t = ty
  let tag = ty_hash
end)

module Mty = Ty.M
module Sty = Ty.S
module Hty = Ty.H

let mk_ty n = Hsty.hashcons {
  ty_node = n;
  ty_tag  = (-1)
}

let mk_ety n = { ty_node = n; ty_tag = -1 }

let mk_G = mk_ty G

let mk_GT = mk_ty GT

let mk_Fq = mk_ty Fq

let mk_Bool = mk_ty Bool

let mk_Prod tys = mk_ty (Prod tys)

(* ----------------------------------------------------------------------- *)

let rec ty_export ty =
  let en = 
    match ty.ty_node with
    | BS lv   -> BS (Lenvar.export lv)
    | Bool    -> Bool
    | G       -> G
    | GT      -> GT
    | Fq      -> Fq
    | Prod ts -> Prod (List.map ty_export ts)
  in mk_ety en

let rec pp_ty fmt ty =
  match ty.ty_node with
  | BS lv   -> Format.fprintf fmt "BS_%a" Lenvar.pp lv
  | Bool    -> Format.fprintf fmt "Bool"
  | G       -> Format.fprintf fmt "G"
  | GT      -> Format.fprintf fmt "GT"
  | Fq      -> Format.fprintf fmt "Fq"
  | Prod ts -> Format.fprintf fmt "(%a)" (pp_list "," pp_ty) ts
