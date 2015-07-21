(*s This module implements hashconsed and non-hashconsed expressions. *)

(*i*)
open Abbrevs
open Util
open Type
open Syms
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Expression data types} *)

type proj_type = ty * ty * ty

type perm_type = IsInv | NotInv

let hash_perm_type = function
  | IsInv  -> 1
  | NotInv -> 2

let key_elem_of_perm_type = function
  | IsInv  -> SKey
  | NotInv -> PKey

(** Constants. *)
type cnst =
    GGen        (*r generator of $\group$ (type defines group) *)
  | FNat of int (*r Natural number in field, always $\geq 0$ *)
  | Z           (*r $0$ bitstring (type defines length) *)
  | B of bool   (*r boolean value *)

(** Hash constants. *)
let cnst_hash = (*c ... *) (*i*)
  function
  | GGen   -> 1
  | FNat n -> Hashcons.combine 2 n
  | Z      -> 3
  | B b    -> if b then 4 else 5
(*i*)

(** Operators with fixed arity. *)
type op =
 | GExp of Groupvar.id        (*r exponentiation in $\group_i$ *)
 | GLog of Groupvar.id        (*r discrete logarithm in $\group_i$ *)
 | GInv                       (* inverse in group *)
 | FOpp                       (*r additive inverse in $\field$ *)
 | FMinus                     (*r subtraction in $\field$ *)
 | FInv                       (*r mult. inverse in $\field$ *)
 | FDiv                       (*r division in $\field$ *)
 | Eq                         (*r equality *)
 | Not                        (*r negation *)
 | Ifte                       (*r if then else *)
 | EMap of Esym.t             (*r bilinear map *)
 | Perm of perm_type * Psym.t (*r permutation or inverse *)

(** Hash operators. *)
let op_hash = (*c ... *) (*i*)
  function
  | GExp gv  -> hcomb 1 (Groupvar.hash gv)
  | GLog gv  -> hcomb 2 (Groupvar.hash gv)
  | GInv     -> 3
  | FOpp     -> 4
  | FMinus   -> 5
  | FInv     -> 6
  | FDiv     -> 7
  | Eq       -> 8
  | Not      -> 9
  | Ifte     -> 10
  | EMap es  -> hcomb 11 (Esym.hash es)
  | Perm(pt,f) -> hcomb (hash_perm_type pt) (Psym.hash f)
  (*i*)

(** N-ary/associative operators with variable arity. *)
type nop =
    FPlus  (*r plus in Fq *)
  | FMult  (*r multiplication in Fq *)
  | Xor    (*r Xor of bitstrings *)
  | Land   (*r logical and *)
  | GMult  (*r multiplication in G (type defines group) *)

(** Hash n-ary operators. *)
let nop_hash = (*c ... *) (*i*)
  function
  | FPlus  -> 1
  | FMult  -> 2
  | Xor    -> 3
  | Land   -> 4
  | GMult  -> 5
(*i*)

type quant = All | Exists

let neg_quant q = if q = All then Exists else All

let hash_quant = function
  | All    -> 1
  | Exists -> 2

(** Expressions and expression nodes. *)
type expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_tag  : int
}
and expr_node =
  | V           of Vsym.t          (*r variables (program, logical, random, ...) *)
  | H           of Hsym.t * expr   (*r hash function application *)
  | Tuple       of expr list       (*r tuples *)
  | Proj        of int * expr      (*r projection *)
  | Cnst        of cnst            (*r constants *)
  | App         of op * expr list  (*r fixed arity operators *)
  | Nary        of nop * expr list (*r variable arity AC operators *)
  | Quant       of quant * (Vsym.t list * Oracle.t) * expr
  | ProjPermKey of key_elem * expr	       

(** Equality hashing, and comparison for expressions. *)
let e_equal : expr -> expr -> bool = (==) 
let e_hash e = e.e_tag
let e_compare e1 e2 = e1.e_tag - e2.e_tag

(** Hashcons expressions. *)
module Hse = Hashcons.Make (struct
  type t = expr

  let equal e1 e2 = (*c ... *) (*i*)
    ty_equal e1.e_ty e2.e_ty &&
    match e1.e_node, e2.e_node with
    | V v1, V v2                 -> Vsym.equal v1 v2
    | H(f1,e1), H(f2,e2)         -> Hsym.equal f1 f2 && e_equal e1 e2
    | Tuple es1, Tuple es2       -> list_eq_for_all2 e_equal es1 es2
    | Proj(i1,e1), Proj(i2,e2)   -> i1 = i2 && e_equal e1 e2
    | Cnst c1, Cnst c2           -> c1 = c2
    | App(o1,es1), App(o2,es2)   -> o1 = o2 && list_eq_for_all2 e_equal es1 es2
    | Nary(o1,es1), Nary(o2,es2) -> o1 = o2 && list_eq_for_all2 e_equal es1 es2
    | Quant(q1,b1,e1), Quant(q2,b2,e2) ->
      q1 = q2 &&
        (pair_equal (list_equal Vsym.equal) Oracle.equal) b1 b2 &&
        e_equal e1 e2
    | ProjPermKey(ke1,e1), ProjPermKey(ke2,e2) ->
      ke1 = ke2 && e_equal e1 e2
    | _, _ -> false
  (*i*)

  let hash_node = (*c ... *) (*i*)
    function
    | V(v)       -> Vsym.hash v
    | H(f,e)     -> hcomb (Hsym.hash f) (e_hash e)
    | ProjPermKey(ke,e) -> hcomb 2 (hcomb (Type.hash_key_elem ke) (e_hash e))
    | Tuple(es)  -> hcomb_l e_hash 3 es
    | Proj(i,e)  -> hcomb i (e_hash e)
    | Cnst(c)    -> cnst_hash c
    | App(o,es)  -> hcomb_l e_hash (op_hash o) es
    | Nary(o,es) -> hcomb_l e_hash (nop_hash o) es
    | Quant(q,(vs,o),e) ->
      hcomb_h
        [ hash_quant q
        ; hcomb_h (List.map Vsym.hash vs)
        ; Oracle.hash o
        ; e_hash e ]
  (*i*)

  let hash e = hcomb (ty_hash e.e_ty) (hash_node e.e_node)

  let tag n e = { e with e_tag = n }
end)

(** Create internal expression. *)
let mk_e n ty = Hse.hashcons {
  e_node = n;
  e_ty   = ty;
  e_tag  = (-1)
}

(** Create Map, Set, and HashTable modules. *)
module E = StructMake (struct
  type t = expr
  let tag = e_hash
end)
module Me = E.M
module Se = E.S
module He = E.H

(*i ----------------------------------------------------------------------- i*)
(*  \hd{Constructor functions} *)

exception TypeError of (ty * ty * expr * expr option * string)

let ensure_ty_equal ty1 ty2 e1 e2 s =
  ignore (ty_equal ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

let ensure_ty_KeyPair ty s =
  match ty.ty_node with
  | KeyPair pid -> pid
  | _ -> failwith (fsprintf "%s: KeyPair arg expected, got %a instead" s pp_ty ty)
              
let ensure_ty_KeyElem ke ty s =
  match ty.ty_node with
  | KeyElem(ke',pid) when ke = ke' -> pid
  | _ ->
    failwith (fsprintf "%s: %s expected, got %a instead" s (string_of_key_elem ke) pp_ty ty)

let ensure_ty_G ty s =
  match ty.ty_node with
  | G gv -> gv
  | _    ->
    failwith (fsprintf "%s: expected group type, got %a" s pp_ty ty)

let mk_V v = mk_e (V v) v.Vsym.ty
  
let mk_H h e =
  ensure_ty_equal h.Hsym.dom e.e_ty e None (fsprintf "mk_H for %a" Hsym.pp h);
  mk_e (H(h,e)) h.Hsym.codom
	 
let mk_ProjPermKey ke kp =
  let kp_pid = ensure_ty_KeyPair kp.e_ty "mk_ProjPermKey" in
  mk_e (ProjPermKey(ke,kp)) (mk_KeyElem ke kp_pid)
       
let mk_Quant q b e =
  mk_e (Quant(q,b,e)) mk_Bool

let mk_All = mk_Quant All

let mk_Exists = mk_Quant Exists

let mk_Tuple es =
  match es with
  | [e] -> e
  | _   -> mk_e (Tuple es) (mk_Prod (L.map (fun e -> e.e_ty) es))

let mk_Proj i e = 
  match e.e_ty.ty_node with
  | Prod(tys) when i >= 0 && L.length tys > i -> 
    mk_e (Proj(i,e)) (L.nth tys i)
  | _ ->
    let s =
      F.sprintf
        "mk_Proj expects product type with at least %i components"
        (i+1)
    in
    raise (TypeError(e.e_ty,e.e_ty,e,None,s))
  
let mk_Cnst c ty = mk_e (Cnst c) ty

let mk_GGen gv = mk_Cnst GGen (mk_G gv)
let mk_FNat n = assert (n >= 0); mk_Cnst (FNat n) mk_Fq
let mk_FOne = mk_Cnst (FNat 1) mk_Fq
let mk_FZ = mk_Cnst (FNat 0) mk_Fq
let mk_Z lv = mk_Cnst Z (mk_BS lv)
let mk_B  b = mk_Cnst (B b) mk_Bool
let mk_True = mk_B true
let mk_False = mk_B false

let mk_App o es ty = mk_e (App(o,es)) ty

let mk_GExp a b =
  let gv = ensure_ty_G a.e_ty "mk_GExp" in
  ensure_ty_equal b.e_ty mk_Fq b None "mk_GExp";
  mk_App (GExp gv) [a;b] a.e_ty

let mk_Perm f ptype k e =
  let ke = key_elem_of_perm_type ptype in
  let k_pid = ensure_ty_KeyElem ke k.e_ty "mk_Perm - key" in
  if (not (f.Psym.pid = k_pid)) then
    failwith (fsprintf "mk_Perm: The permutation of given Key is not %a." Psym.pp f);
  ensure_ty_equal e.e_ty f.Psym.dom
    e (Some k)
    (fsprintf "mk_Perm for %a : expected arg of type %a" Psym.pp f pp_ty e.e_ty);
  let p = Perm(ptype,f) in
  mk_App p [k;e] e.e_ty
                  
let mk_GOne gn =
  mk_GExp (mk_GGen gn) mk_FZ

let mk_GLog a =
  let gv = ensure_ty_G a.e_ty "mk_GLog" in
  mk_App (GLog gv) [a] mk_Fq

let mk_GInv a =
  let _gv = ensure_ty_G a.e_ty "mk_GInv" in
  mk_App GInv  [a] a.e_ty

let mk_EMap es a b =
  ensure_ty_equal a.e_ty (mk_G es.Esym.source1) a None "mk_EMap";
  ensure_ty_equal b.e_ty (mk_G es.Esym.source2) b None "mk_EMap";
  mk_App (EMap es) [a;b] (mk_G es.Esym.target)

let mk_FOpp a =
  ensure_ty_equal a.e_ty mk_Fq a None "mk_FOpp";
  mk_App FOpp [a] mk_Fq

let mk_FMinus a b =
  ensure_ty_equal a.e_ty mk_Fq a None "mk_FMinus";
  ensure_ty_equal b.e_ty mk_Fq b None "mk_FMinus";
  mk_App FMinus [a;b] mk_Fq

let mk_FInv a =
  ensure_ty_equal a.e_ty mk_Fq a None "mk_FInv";
  mk_App FInv [a] mk_Fq

let mk_FDiv a b =
  ensure_ty_equal a.e_ty mk_Fq a None "mk_FDiv";
  ensure_ty_equal b.e_ty mk_Fq b None "mk_FDiv";
  mk_App FDiv [a;b] mk_Fq

let mk_Eq a b =
  ensure_ty_equal a.e_ty b.e_ty a (Some b) "mk_Eq";
  mk_App Eq [a;b] mk_Bool

let mk_Not a =
  ensure_ty_equal a.e_ty mk_Bool a None "mk_Not";
  mk_App Not [a] mk_Bool

let mk_Ifte a b c =
  ensure_ty_equal a.e_ty mk_Bool a None "mk_Ifte";
  ensure_ty_equal b.e_ty c.e_ty b (Some c) "mk_Ifte";
  mk_App Ifte [a;b;c] b.e_ty

let rec flatten nop es =
  let go e = match e.e_node with
    | Nary(nop1, es1) when nop1 = nop ->
      flatten nop es1
    | _ -> [ e ]
  in
  L.concat (L.map go es)

let mk_nary s sort o es ty =
  let es = flatten o es in
  let es = if sort then L.sort e_compare es else es in
  match es with
  | []  -> failwith (F.sprintf "%s: empty list given" s);
  | [a] -> a
  | _   ->
    L.iter (fun e -> ensure_ty_equal e.e_ty ty e None s) es;
    mk_e (Nary(o,es)) ty

let mk_FPlus es = mk_nary "mk_FPlus" true FPlus es mk_Fq 

let mk_FMult es = mk_nary "mk_FMult" true FMult es mk_Fq

(* Helper to check the validity of the type of expressions when calling mk_Xor :
   Every base type must be either Bool or BS, and
   if there ever is a product (stored in acc_option), 
   all the remaining ty_nodes must be of the same type *)
let rec valid_Xor_type ?acc_option acc2 : ty list -> bool = function
  | [] -> true
  | ty::tys when acc_option = None ->
     (match ty.ty_node with
     | BS _ | Bool -> valid_Xor_type (ty::acc2) tys
     | Prod tys2 -> (valid_Xor_type [] tys2) &&
                      (valid_Xor_type ~acc_option:tys2 [] acc2) && 
                        (valid_Xor_type ~acc_option:tys2 [] tys)
     | _ -> false)
  | ty::tys ->
     let Some acc = acc_option in
     (match ty.ty_node with
      | Prod tys2 ->
         (List.fold_left (fun b1 b2 -> b1 && b2) true (List.map2 ty_equal acc tys2))
       (* The previous check also implicitly runs 'valid_Xor_type tys2' due to wf of acc *)
         && (valid_Xor_type ?acc_option [] tys)
      | _ -> false)
                    
let mk_Xor = function
  | e::_ as es -> if ( valid_Xor_type [] (List.map (fun e -> e.e_ty) es) )
                  then mk_nary "mk_Xor" true Xor es e.e_ty
                  else failwith "mk_Xor: type mismatch"
  | _ -> failwith "mk_Xor: expected non-empty list"
                                  
let mk_Land es = mk_nary "mk_Land" false Land es mk_Bool

let mk_GMult es =
  match es with
  | e::_ ->
    begin match e.e_ty.ty_node with
    | G gv -> mk_nary "mk_GMult" true GMult es (mk_G gv)
    | _ -> assert false
    end
  | _ -> assert false

let mk_Nary op es =
  match op with
  | FPlus -> mk_FPlus es
  | FMult -> mk_FMult es
  | Xor   -> mk_Xor   es
  | Land  -> mk_Land  es
  | GMult -> mk_GMult es

let mk_InEq a b =
  mk_Not (mk_Eq a b)
  (*i ----------------------------------------------------------------------- i*)
(* \hd{Generic functions on expressions} *)

let sub_map g e = 
  match e.e_node with
  | V _ | Cnst _ -> e
  | H(h,e1) ->
      let e1' = g e1 in
      if e1 == e1' then e
      else mk_e (H(h, e1')) e.e_ty
  | ProjPermKey(ke,e1) ->
     let e1' = g e1 in
     if e1 == e1' then e
     else mk_e (ProjPermKey(ke,e1')) e.e_ty
  | Tuple(es) ->
      let es' = smart_map g es in
      if es == es' then e
      else mk_e (Tuple es') e.e_ty
  | Proj(i, e1) ->
      let e1' = g e1 in
      if e1 == e1' then e
      else mk_e (Proj(i, e1')) e.e_ty
  | App(o, es) ->
      let es' = smart_map g es in
      if es == es' then e
      else mk_e (App(o, es')) e.e_ty
  | Nary(o, es) ->
      let es' = smart_map g es in
      if es == es' then e
      else mk_e (Nary(o, es')) e.e_ty
  | Quant(q,b,e1) ->
    let e' = g e1 in
    if e1 == e' then e
    else mk_Quant q b e'

let check_fun g e =
  let e' = g e in 
  ensure_ty_equal e'.e_ty e.e_ty e (Some e') "check_fun";
  e'

let e_sub_map g = sub_map (check_fun g)

let e_sub_fold g acc e =
  match e.e_node with
  | V _ | Cnst _ -> acc
  | ProjPermKey(_,e) | H(_,e) | Proj(_, e) | Quant(_,_,e) -> g acc e
  | Tuple(es) | App(_, es) | Nary(_, es)-> L.fold_left g acc es

let e_sub_iter g e = 
  match e.e_node with
  | V _ | Cnst _ -> ()
  | ProjPermKey(_,e) | H(_,e) | Proj(_, e) | Quant(_,_,e) -> g e
  | Tuple(es) | App(_, es) | Nary(_, es)-> L.iter g es

let rec e_iter g e =
  g e; e_sub_iter (e_iter g) e

let e_sub_exists f =
  e_sub_fold (fun acc e -> acc || f e) false

let rec e_exists f e =
  f e || e_sub_exists (e_exists f) e

let e_sub_forall f =
  e_sub_fold (fun acc e -> acc && f e) true

let rec e_forall f e = 
  f e && e_sub_forall (e_forall f) e

let e_find f (e : expr) = 
  let module E = struct exception Found of expr end in
  let rec aux e = 
    if f e then raise (E.Found e)
    else e_sub_iter aux e in
  try aux e; raise Not_found with E.Found e -> e

let e_find_all f e =
  let rec aux s e =
    let s = if f e then Se.add e s else s in
    e_sub_fold aux s e in
  aux Se.empty e

let e_map f =
  let tbl = He.create 103 in
  let rec aux e = 
    try He.find tbl e 
    with _ ->
      let e' = f (sub_map aux e) in
      ensure_ty_equal e'.e_ty e.e_ty e (Some e') "e_rec_map";
      He.add tbl e e';
      e' in
  aux

let e_map_ty_maximal ty g e0 =
  let rec go ie e =
    (* me = e is a maximal expression of the desired type *)
    let me = not ie && ty_equal e.e_ty ty in
    (* ie = immediate subterms of e are inside a larger expression of the desired type *)
    let ie = me || (ie && ty_equal e.e_ty ty) in
    let trans = if me then g else id in
    match e.e_node with
    | V(_) | Cnst(_) -> e
    | ProjPermKey(ke,kp) ->
       let kp = go ie kp in
       trans (mk_ProjPermKey ke kp)
    | H(f,e) ->
      let e = go ie e in
      trans (mk_H f e)
    | Tuple(es) ->
      let es = L.map (go ie) es in
      trans (mk_Tuple es)
    | Quant (q,b,e) ->
      let e = go ie e in
      trans (mk_Quant q b e)      
    | Proj(i,e) ->
      let e = go ie e in
      trans (mk_Proj i e)
    | App(o,es) ->
      let es = L.map (go ie) es in
      trans (mk_App o es e.e_ty) 
    | Nary(o,es) -> 
      let es = L.map (go ie) es in
      trans (mk_Nary o es) 
  in
  go false e0

let e_map_top f = 
  let tbl = He.create 103 in
  let rec aux e =
    try He.find tbl e 
    with Not_found ->
      let e' = try check_fun f e with Not_found -> sub_map aux e in
      He.add tbl e e';
      e'
  in
  aux 

let e_replace e1 e2 = 
  e_map_top (fun e -> if e_equal e e1 then e2 else raise Not_found)

let e_subst s =
  e_map_top (fun e -> Me.find e s)
