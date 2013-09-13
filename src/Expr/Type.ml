open Util
open IdType

module Tyvar : IdType.ID = Id

type 'a gty = {
  ty_sum : ('a Tyvar.gid) list; (* a list, i.e., types are associative *)
  ty_tag : int
}

type ty = internal gty
type ety = exported gty

let ty_equal : ty -> ty -> bool = (==)

let ty_hash t = t.ty_tag

module Hsty = Hashcons.Make (struct
  type t = ty
  let equal t1 t2 = list_eq_for_all2 Tyvar.equal t1.ty_sum t2.ty_sum
  let hash t = Hashcons.combine_list Tyvar.hash 0 t.ty_sum
  let tag n t = { t with ty_tag = n }
end)

module Ty = StructMake (struct
  type t = ty
  let tag = ty_hash
end)

module Mty = Ty.M
module Sty = Ty.S
module Hty = Ty.H

let mk_ty vs = Hsty.hashcons {
  ty_sum = vs;
  ty_tag = (-1)
}

let is_ty_var t = List.length (t.ty_sum) = 1

let is_ty_zero t = t.ty_sum = []

let ty_minus a b =
  let rec dropCommon xs ys = 
    match xs,ys with
    | _, []                   -> Some(mk_ty xs)
    | x::xs, y::ys when x = y -> dropCommon xs ys
    | _                       -> None
  in dropCommon a.ty_sum b.ty_sum

(* ----------------------------------------------------------------------- *)

module Hty2 = Hashtbl.Make (struct
  type t = ty * ty
  let equal (t11,t12) (t21,t22) =
    ty_equal t11 t21 && ty_equal t12 t22
  let hash (t1,t2) = Hashcons.combine (ty_hash t1) (ty_hash t2)
end)

let concat_tbl = Hty2.create 5003

let ty_concat t1 t2 =
  let key = (t1,t2) in
  try Hty2.find concat_tbl key
  with Not_found ->
    let l = t1.ty_sum @ t2.ty_sum in
    let t = mk_ty l in
    Hty2.add concat_tbl key t;
    t

let ty_concat_l l =
  match l with
  | [] -> mk_ty []
  | t::lt -> List.fold_left ty_concat t lt

(* ----------------------------------------------------------------------- *)

let ty_export ty = (* FIXME: Is there a way to use deep coercion? *)
  { ty_sum = List.map Tyvar.export ty.ty_sum; ty_tag = -1 }

let mk_ety vs = { ty_sum = vs; ty_tag = -1 }

let pp_ty fmt t =
  match t.ty_sum with
  | [] -> Format.fprintf fmt "0"
  | l  -> (pp_list "+" Tyvar.pp) fmt l
