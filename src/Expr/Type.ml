(*s This module implements hashconsed and non-hashconsed types. *)

(*i*)
open Util
(*i*)

(** Identifier for (bitstring) length and group variables. *)
module Lenvar : IdType.ID = Id
module Groupvar : IdType.ID = Id

(** Types and type nodes. *)
type ty = {
  ty_node : ty_node;
  ty_tag : int
}
and ty_node =
  | BS of Lenvar.id
  | Bool
  | G of Groupvar.id
  | Fq
  | Prod of ty list


(** Type equality and hashing. *)
let ty_equal : ty -> ty -> bool = (==)
let ty_hash t = t.ty_tag

(** Hashconsing for types. *)
module Hsty = Hashcons.Make (struct
  type t = ty

  let equal t1 t2 = match t1.ty_node, t2.ty_node with
    | BS lv1, BS lv2     -> Lenvar.equal lv1 lv2
    | Bool, Bool         -> true
    | G gv1, G gv2       -> Groupvar.equal gv1 gv2
    | Fq, Fq             -> true
    | Prod ts1, Prod ts2 -> list_eq_for_all2 ty_equal ts1 ts2
    | _                  -> false

  let hash t = match t.ty_node with
    | BS lv   -> Hashcons.combine 1 (Lenvar.hash lv)
    | Bool    -> 2
    | G gv    -> Hashcons.combine 3 (Groupvar.hash gv)
    | Fq      -> 4
    | Prod ts -> Hashcons.combine_list ty_hash 3 ts

  let tag n t = { t with ty_tag = n }
end)

(** Create [Map], [Set], and [Hashtbl] modules for types. *)
module Ty = StructMake (struct
  type t = ty
  let tag = ty_hash
end)
module Mty = Ty.M
module Sty = Ty.S
module Hty = Ty.H

(** Create type. *)
let mk_ty n = Hsty.hashcons {
  ty_node = n;
  ty_tag  = (-1)
}

(** Create types: bitstring, group, field, boolean, tuple. *)
let mk_BS lv = mk_ty (BS lv)
let mk_G gv = mk_ty (G gv)
let mk_Fq = mk_ty Fq
let mk_Bool = mk_ty Bool
let mk_Prod tys = mk_ty (Prod tys)

(** Indicator functions for types. *)
let is_G ty = match ty.ty_node with
  | G _ -> true
  | _ -> false
let is_Fq ty = match ty.ty_node with
  | Fq -> true
  | _  -> false

(** Destructor functions for types. *)
let destr_G ty = match ty.ty_node with
  | G gv -> gv
  | _    -> assert false
let destr_BS ty = 
  match ty.ty_node with
  | BS lv -> lv
  | _     -> assert false
let destr_Prod ty = match ty.ty_node with
  | Prod ts -> ts
  | _ -> assert false

(*i ----------------------------------------------------------------------- i*)

(*i*)
let rec pp_ty fmt ty =
  match ty.ty_node with
  | BS lv   -> F.fprintf fmt "BS_%s" (Lenvar.name lv)
  | Bool    -> F.fprintf fmt "Bool"
  | Fq      -> F.fprintf fmt "Fq"
  | Prod ts -> F.fprintf fmt "(%a)" (pp_list " * " pp_ty) ts
  | G gv when Groupvar.name gv = "" ->
    F.fprintf fmt "G" 
  | G gv    -> F.fprintf fmt "G_%s" (Groupvar.name gv)

(*i*)
