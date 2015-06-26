(*s This module implements hashconsed and non-hashconsed types. *)

(*i*)
open Abbrevs
open Util
(*i*)

(** Identifier for (bitstring) length and group variables. *)
module Lenvar : IdType.ID = Id
module Groupvar : IdType.ID = Id
module Permvar : IdType.ID = Id
			       
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
  | Int 
  | KeyPair of Permvar.id
  | PKey of Permvar.id
  | SKey of Permvar.id

(** Type equality and hashing. *)
let ty_equal : ty -> ty -> bool = (==)
let ty_hash t = t.ty_tag
let ty_compare t1 t2 = t1.ty_tag - t2.ty_tag

(** Hashconsing for types. *)
module Hsty = Hashcons.Make (struct
  type t = ty

  let equal t1 t2 = match t1.ty_node, t2.ty_node with
    | BS lv1, BS lv2     -> Lenvar.equal lv1 lv2
    | Bool, Bool         -> true
    | G gv1, G gv2       -> Groupvar.equal gv1 gv2
    | KeyPair pv1, KeyPair pv2
    | PKey pv1, PKey pv2
    | SKey pv1, SKey pv2   -> Permvar.equal pv1 pv2
    | Fq, Fq             -> true
    | Prod ts1, Prod ts2 -> list_eq_for_all2 ty_equal ts1 ts2
    | _                  -> false

  let hash t = match t.ty_node with
    | BS lv   -> Hashcons.combine 1 (Lenvar.hash lv)
    | Bool    -> 2
    | G gv    -> Hashcons.combine 3 (Groupvar.hash gv)
    | Fq      -> 4
    | Prod ts -> Hashcons.combine_list ty_hash 3 ts
    | Int     -> 6
    | KeyPair pv -> Hashcons.combine 7 (Permvar.hash pv)
    | PKey pv    -> Hashcons.combine 8 (Permvar.hash pv)
    | SKey pv    -> Hashcons.combine 9 (Permvar.hash pv)

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
let mk_KeyPair pv = mk_ty (KeyPair pv)
let mk_PKey pv = mk_ty (PKey pv)
let mk_SKey pv = mk_ty (SKey pv)
let mk_Fq = mk_ty Fq
let mk_Bool = mk_ty Bool
let mk_Int = mk_ty Int
let mk_Prod tys = 
  match tys with
  | [t] -> t 
  | _ -> mk_ty (Prod tys)

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

let destr_P ty = 
  match ty.ty_node with
  | KeyPair lv -> lv
  | PKey lv -> lv
  | SKey lv -> lv
  | _     -> assert false

let destr_Prod ty = match ty.ty_node with
  | Prod ts -> ts
  | _ -> assert false

(*
(*i ----------------------------------------------------------------------- i*)
(** Check size equality of type *)
type size = {
  mutable s_BS : Id.S.t;
  mutable s_B  : int;
  mutable s_G  : Id.S.t;
  mutable s_Fq : int
}

let size_of t = 
  let s = { s_Bs = Id.S.empty; s_B = 0; s_G = Id.S.empty;s_Fq = 0 } in
  let rec aux ty = 
    match ty.ty_node with
    | BS id  -> s.s_Bs <- Id.S.add id s.s_Bs 
    | Bool   -> s.s_B  <- 1 + s.s_B
    | G id   -> s.s_G  <- Id.S.add id s.s_G
    | Fq     -> s.s_Fq <- 1 + s.s_Fq
    | Prod l -> List.iter aux l
    | Int    -> assert false in
  aux ty;
  s
*)

(*i ----------------------------------------------------------------------- i*)

(*i*)

let pp_group fmt gv =
  if Groupvar.name gv = ""
  then F.fprintf fmt "G"
  else F.fprintf fmt "G_%s" (Groupvar.name gv)

let rec pp_ty fmt ty =
  match ty.ty_node with
  | BS lv   -> F.fprintf fmt "BS_%s" (Lenvar.name lv)
  | Bool    -> F.fprintf fmt "Bool"
  | Fq      -> F.fprintf fmt "Fq"
  | Prod ts -> F.fprintf fmt "(%a)" (pp_list " * " pp_ty) ts
  | G gv when Groupvar.name gv = "" ->
    F.fprintf fmt "G" 
  | G gv    -> F.fprintf fmt "G_%s" (Groupvar.name gv)
  | Int     -> F.fprintf fmt "Int"
  | KeyPair pv    -> F.fprintf fmt "KeyPair_%s" (Permvar.name pv)
  | PKey pv    -> F.fprintf fmt "PKey_%s" (Permvar.name pv)
  | SKey pv    -> F.fprintf fmt "SKey_%s" (Permvar.name pv)

(*i*)
