(* * Types (hashconsed) *)

(* ** Imports *)
open Abbrevs
open Util

(* ** Identifiers *)

module Lenvar : IdType.ID = Id

module Groupvar : IdType.ID = Id

module Permvar : IdType.ID = Id

(* ** Permutation keys *)

module KeyElem = struct
  type t = SKey | PKey
    with compare
  
  let hash = Hashtbl.hash

  let equal ke1 ke2 =
    compare ke1 ke2 = 0

  let pp fmt = function
    | SKey -> pp_string fmt "SKey"
    | PKey -> pp_string fmt "Pkey"
end

(* ** Types and type nodes *)

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
  | KeyElem of KeyElem.t * Permvar.id

(* ** Equality, hashing, and hash consing *)

let equal_ty : ty -> ty -> bool = (==)
let hash_ty t = t.ty_tag
let compare_ty t1 t2 = t1.ty_tag - t2.ty_tag

module Hsty = Hashcons.Make (struct
  type t = ty

  let equal t1 t2 =
    match t1.ty_node, t2.ty_node with
    | BS lv1, BS lv2                 -> Lenvar.equal lv1 lv2
    | Bool, Bool                     -> true
    | G gv1, G gv2                   -> Groupvar.equal gv1 gv2
    | Fq, Fq                         -> true
    | Prod ts1, Prod ts2             -> list_eq_for_all2 equal_ty ts1 ts2
    | KeyPair p1, KeyPair p2         -> Permvar.equal p1 p2
    | KeyElem(k1,p1), KeyElem(k2,p2) -> KeyElem.equal k1 k2 && Permvar.equal p1 p2
    | _                              -> false

  let hash t =
    match t.ty_node with
    | BS lv         -> hcomb 1 (Lenvar.hash lv)
    | Bool          -> 2
    | G gv          -> hcomb 3 (Groupvar.hash gv)
    | Fq            -> 4
    | Prod ts       -> hcomb_l hash_ty 3 ts
    | Int           -> 6
    | KeyPair p     -> hcomb 7 (Permvar.hash p)
    | KeyElem(ke,p) -> hcomb 8 (hcomb (KeyElem.hash ke) (Permvar.hash p))

  let tag n t = { t with ty_tag = n }
end)

(** Create [Map], [Set], and [Hashtbl] modules for types. *)
module Ty = StructMake (struct
  type t = ty
  let tag = hash_ty
end)
module Mty = Ty.M
module Sty = Ty.S
module Hty = Ty.H

(* ** Constructor functions *)

let mk_ty n = Hsty.hashcons {
  ty_node = n;
  ty_tag  = (-1)
}

let mk_BS lv = mk_ty (BS lv)

let mk_G gv = mk_ty (G gv)

let mk_KeyPair pid = mk_ty (KeyPair pid)

let mk_KeyElem ke pid = mk_ty (KeyElem(ke,pid))

let mk_Fq = mk_ty Fq

let mk_Bool = mk_ty Bool

let mk_Int = mk_ty Int

let mk_Prod tys = 
  match tys with
  | [t] -> t 
  | _   -> mk_ty (Prod tys)

(* ** Indicator and destructor functions *)

let is_G ty = match ty.ty_node with
  | G _ -> true
  | _   -> false

let is_Fq ty = match ty.ty_node with
  | Fq -> true
  | _  -> false

let is_Prod ty = match ty.ty_node with
  | Prod _ -> true
  | _      -> false

let destr_G_exn ty =
  match ty.ty_node with
  | G gv -> gv
  | _    -> raise Not_found

let destr_BS_exn ty = 
  match ty.ty_node with
  | BS lv -> lv
  | _     -> raise Not_found

let destr_KeyPair_exn ty = 
  match ty.ty_node with
  | KeyPair lv -> lv
  | _          -> raise Not_found

let destr_KeyElem_exn ty = 
  match ty.ty_node with
  | KeyElem(ke,lv) -> (ke,lv)
  | _              -> raise Not_found

let destr_Prod_exn ty =
  match ty.ty_node with
  | Prod ts -> ts
  | _       -> raise Not_found

let destr_Prod ty =
  match ty.ty_node with
  | Prod ts -> Some ts
  | _       -> None

(* ** Pretty printing *)

let pp_group fmt gv =
  if Groupvar.name gv = ""
  then F.fprintf fmt "G"
  else F.fprintf fmt "G_%s" (Groupvar.name gv)

let rec pp_ty fmt ty =
  let open KeyElem in
  match ty.ty_node with
  | BS lv             -> F.fprintf fmt "BS_%s" (Lenvar.name lv)
  | Bool              -> F.fprintf fmt "Bool"
  | Fq                -> F.fprintf fmt "Fq"
  | Prod ts           -> F.fprintf fmt "(%a)" (pp_list " * " pp_ty) ts
  | Int               -> F.fprintf fmt "Int"
  | KeyPair pid       -> F.fprintf fmt "KeyPair_%s" (Permvar.name pid)
  | KeyElem(SKey,pid) -> F.fprintf fmt "PKey_%s" (Permvar.name pid)
  | KeyElem(PKey,pid) -> F.fprintf fmt "SKey_%s" (Permvar.name pid)
  | G gv ->
    if Groupvar.name gv = ""
    then F.fprintf fmt "G" 
    else F.fprintf fmt "G_%s" (Groupvar.name gv)
