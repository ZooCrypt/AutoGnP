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

(** Constants. *)
type cnst =
    GGen        (*r generator of $\group$ (type defines group) *)
  | FNat of int (*r Natural number in field, always $\geq 0$ *)
  | Z           (*r $0$ bitstring (type defines length) *)
  | B of bool   (*r boolean value *)
(* | PermKey of bool (*r permutation key (type defines Perm) *) *)


(** Hash constants. *)
let cnst_hash = (*c ... *) (*i*)
  function
  | GGen   -> 1
  | FNat n -> Hashcons.combine 2 n
  | Z      -> 3
  | B b    -> if b then 5 else 6
(*i*)


(** Operators with fixed arity. *)
type op =
    GExp of Groupvar.id  (*r exponentiation in $\group_i$ *)
  | GLog of Groupvar.id  (*r discrete logarithm in $\group_i$ *)
  | GInv                 (* inverse in group *)
  | FOpp                 (*r additive inverse in $\field$ *)
  | FMinus               (*r subtraction in $\field$ *)
  | FInv                 (*r mult. inverse in $\field$ *)
  | FDiv                 (*r division in $\field$ *)
  | Eq                   (*r equality *)
  | Not                  (*r negation *)
  | Ifte                 (*r if then else *)
  | EMap of Esym.t       (*r bilinear map *)

(** Hash operators. *)
let op_hash = (*c ... *) (*i*)
  function
  | GExp gv  -> Hashcons.combine 1 (Groupvar.hash gv)
  | GLog gv  -> Hashcons.combine 2 (Groupvar.hash gv)
  | GInv     -> 3
  | FOpp     -> 4
  | FMinus   -> 5
  | FInv     -> 6
  | FDiv     -> 7
  | Eq       -> 8
  | Not      -> 9
  | Ifte     -> 10
  | EMap es  -> Hashcons.combine 11 (Esym.hash es)
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


(** Expressions and expression nodes. *)
type expr = {
  e_node : expr_node;
  e_ty   : ty;
  e_tag  : int
}
and expr_node =
  | V      of Vsym.t          (*r variables (program, logical, random, ...) *)
  | H      of Hsym.t * expr   (*r hash function application *)
  | Tuple  of expr list       (*r tuples *)
  | Proj   of int * expr      (*r projection *)
  | Cnst   of cnst            (*r constants *)
  | App    of op * expr list  (*r fixed arity operators *)
  | Nary   of nop * expr list (*r variable arity AC operators *)
  | All of (Vsym.t list * Oracle.t) list * expr
  | Perm of Psym.t * bool * expr * expr  (*r OW permutation (f,is_inverse,Key,e) *)
  | GetPK of Psym.t * expr          (*r Public Key of f required by f *)  
  | GetSK of Psym.t * expr          (*r Secret Key of f required by f_inv *)
	       

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
    | App(Eq,[e11;e12]), App(Eq,[e21;e22]) -> (* commutativity *)
       (e_equal e11 e21 && e_equal e12 e22) || (e_equal e11 e22 && e_equal e12 e21)
    | App(o1,es1), App(o2,es2)   -> o1 = o2 && list_eq_for_all2 e_equal es1 es2
    | Nary(o1,es1), Nary(o2,es2) -> o1 = o2 && list_eq_for_all2 e_equal es1 es2
    | All(b1,e1), All(b2,e2) ->
      list_equal (pair_equal (list_equal Vsym.equal) Oracle.equal) b1 b2 &&
        e_equal e1 e2
    | Perm(f1,b1,k1,e1), Perm(f2,b2,k2,e2)
      -> Psym.equal f1 f2 && b1=b2 && e_equal k1 k2 && e_equal e1 e2
    | GetPK(f1,kp1), GetPK(f2,kp2) | GetSK(f1,kp1), GetSK(f2,kp2) ->
        (Psym.equal f1 f2) && e_equal kp1 kp2
    | _, _                       -> false
  (*i*)

  let hash_node = (*c ... *) (*i*)
    function
    | V(v)       -> Vsym.hash v
    | H(f,e)     -> Hashcons.combine (Hsym.hash f) (e_hash e)
    | Perm(f,b,k,e) -> let hc = Hashcons.combine in
		       hc (if b then 1 else 2) (hc (Psym.hash f) (hc (e_hash k) (e_hash e)))
    | GetPK(f,e)   -> Hashcons.combine 1 (Hashcons.combine (e_hash e) (Psym.hash f))
    | GetSK(f,e)   -> Hashcons.combine 2 (Hashcons.combine (e_hash e) (Psym.hash f))
    | Tuple(es)  -> Hashcons.combine_list e_hash 3 es
    | Proj(i,e)  -> Hashcons.combine i (e_hash e)
    | Cnst(c)    -> cnst_hash c
    | App(o,es)  -> Hashcons.combine_list e_hash (op_hash o) es
    | Nary(o,es) -> Hashcons.combine_list e_hash (nop_hash o) es
    | All(b,e) ->
      Hashcons.combine_list 
        (fun (vs,o) ->
          (Hashcons.combine_list Vsym.hash (Oracle.hash o) vs))
        (e_hash e)
        b
  (*i*)

  let hash e = Hashcons.combine (ty_hash e.e_ty) (hash_node e.e_node)

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
                  
let ensure_ty_PKey ty s =
  match ty.ty_node with
  | PKey pid -> pid
  | _    ->
    failwith (fsprintf "%s: PubKey expected, got %a instead" s pp_ty ty)

let ensure_ty_SKey ty s =
  match ty.ty_node with
  | SKey pid -> pid
  | _    ->
    failwith (fsprintf "%s: SecretKey expected, got %a instead" s pp_ty ty)

let ensure_ty_G ty s =
  match ty.ty_node with
  | G gv -> gv
  | _    ->
    failwith (fsprintf "%s: expected group type, got %a" s pp_ty ty)

let ty_G gv = mk_ty (G gv)
(*let ty_KeyPair pid = mk_ty (KeyPair pid) *)
let ty_PKey pid = mk_ty (PKey pid)
let ty_SKey pid = mk_ty (SKey pid)
let ty_Fq = mk_ty Fq
let ty_Bool = mk_ty Bool
let ty_BS lv = mk_ty (BS lv)
let ty_Prod tys = mk_ty (Prod tys)

let mk_V v = mk_e (V v) v.Vsym.ty
  
let mk_H h e =
  ensure_ty_equal h.Hsym.dom e.e_ty e None (fsprintf "mk_H for %a" Hsym.pp h);
  mk_e (H(h,e)) h.Hsym.codom

let mk_Perm f is_inverse k e =
    let k_pid = if is_inverse then
		     ensure_ty_SKey k.e_ty "mk_Perm (inverse) - key"
		   else
		     ensure_ty_PKey k.e_ty "mk_Perm (direct) - key"
    in
    if (not (f.Psym.pid = k_pid)) then
      failwith (fsprintf "mk_Perm: The permutation of given Key is not %a." Psym.pp f);
    ensure_ty_equal e.e_ty f.Psym.dom
		    e (Some k)
		    (fsprintf "mk_Perm for %a : expected arg of type %a" Psym.pp f pp_ty e.e_ty);
    mk_e (Perm(f,is_inverse,k,e)) f.Psym.dom
                  
	 
let mk_GetPK f kp =
  let kp_pid = ensure_ty_KeyPair kp.e_ty "mk_GetPK" in
    if (not (f.Psym.pid = kp_pid)) then
      failwith (fsprintf "mk_GetPK: The permutation of given KeyPair is not %a." Psym.pp f);  
    mk_e (GetPK (f,kp)) (ty_PKey f.Psym.pid)

let mk_GetSK f kp =
  let kp_pid = ensure_ty_KeyPair kp.e_ty "mk_GetSK" in
    if (not (f.Psym.pid = kp_pid)) then
      failwith (fsprintf "mk_GetSK: The permutation of given KeyPair is not %a." Psym.pp f);  
    mk_e (GetSK (f,kp)) (ty_SKey f.Psym.pid)
       
let mk_All b e =
  mk_e (All(b,e)) ty_Bool

let mk_Tuple es =
  match es with
  | [e] -> e
  | _   -> mk_e (Tuple es) (ty_Prod (L.map (fun e -> e.e_ty) es))

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

let mk_GGen gv = mk_Cnst GGen (ty_G gv)
let mk_FNat n = assert (n >= 0); mk_Cnst (FNat n) ty_Fq
let mk_FOne = mk_Cnst (FNat 1) ty_Fq
let mk_FZ = mk_Cnst (FNat 0) ty_Fq
let mk_Z lv = mk_Cnst Z (ty_BS lv)
let mk_B  b = mk_Cnst (B b) ty_Bool
let mk_True = mk_B true
let mk_False = mk_B false

let mk_App o es ty = mk_e (App(o,es)) ty

let mk_GExp a b =
  let gv = ensure_ty_G a.e_ty "mk_GExp" in
  ensure_ty_equal b.e_ty ty_Fq b None "mk_GExp";
  mk_App (GExp gv) [a;b] a.e_ty

let mk_GOne gn =
  mk_GExp (mk_GGen gn) mk_FZ

let mk_GLog a =
  let gv = ensure_ty_G a.e_ty "mk_GLog" in
  mk_App (GLog gv) [a] ty_Fq

let mk_GInv a =
  let _gv = ensure_ty_G a.e_ty "mk_GInv" in
  mk_App GInv  [a] a.e_ty

let mk_EMap es a b =
  ensure_ty_equal a.e_ty (ty_G es.Esym.source1) a None "mk_EMap";
  ensure_ty_equal b.e_ty (ty_G es.Esym.source2) b None "mk_EMap";
  mk_App (EMap es) [a;b] (ty_G es.Esym.target)

let mk_FOpp a =
  ensure_ty_equal a.e_ty ty_Fq a None "mk_FOpp";
  mk_App FOpp [a] ty_Fq

let mk_FMinus a b =
  ensure_ty_equal a.e_ty ty_Fq a None "mk_FMinus";
  ensure_ty_equal b.e_ty ty_Fq b None "mk_FMinus";
  mk_App FMinus [a;b] ty_Fq

let mk_FInv a =
  ensure_ty_equal a.e_ty ty_Fq a None "mk_FInv";
  mk_App FInv [a] ty_Fq

let mk_FDiv a b =
  ensure_ty_equal a.e_ty ty_Fq a None "mk_FDiv";
  ensure_ty_equal b.e_ty ty_Fq b None "mk_FDiv";
  mk_App FDiv [a;b] ty_Fq

let mk_Eq a b =
  ensure_ty_equal a.e_ty b.e_ty a (Some b) "mk_Eq";
  mk_App Eq [a;b] ty_Bool

let mk_Not a =
  ensure_ty_equal a.e_ty ty_Bool a None "mk_Not";
  mk_App Not [a] ty_Bool

let mk_Ifte a b c =
  ensure_ty_equal a.e_ty ty_Bool a None "mk_Ifte";
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

let mk_FPlus es = mk_nary "mk_FPlus" true FPlus es ty_Fq 

let mk_FMult es = mk_nary "mk_FMult" true FMult es ty_Fq

let mk_Xor es =
  match es with
  | e::_ ->
    begin match e.e_ty.ty_node with
    | BS _ | Bool -> mk_nary "mk_Xor" true Xor es e.e_ty
    | _ -> failwith "mk_Xor: expected bitstring argument"
    end
  | _ -> failwith "mk_Xor: expected non-empty list"

let mk_Land es = mk_nary "mk_Land" false Land es ty_Bool

let mk_GMult es =
  match es with
  | e::_ ->
    begin match e.e_ty.ty_node with
    | G gv -> mk_nary "mk_GMult" true GMult es (ty_G gv)
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

(*i ----------------------------------------------------------------------- i*)
(* \hd{Generic functions on expressions} *)

let sub_map g e = 
  match e.e_node with
  | V _ | Cnst _ -> e
  | H(h,e1) ->
      let e1' = g e1 in
      if e1 == e1' then e
      else mk_e (H(h, e1')) e.e_ty
  | Perm(f,is_inverse,k,e1) ->
     let e1' = g e1 in
     let k' = g k in
     if e1 == e1' && k' == k then e
     else mk_e (Perm(f,is_inverse,k',e1')) e.e_ty
  | GetPK(f,e1) ->
     let e1' = g e1 in
     if e1 == e1' then e
     else mk_e (GetPK(f,e1')) e.e_ty
  | GetSK(f,e1) ->
     let e1' = g e1 in
     if e1 == e1' then e
     else mk_e (GetSK(f,e1')) e.e_ty
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
  | All(b,e1) ->
    let e' = g e1 in
    if e1 == e' then e
    else mk_All b e'

let check_fun g e =
  let e' = g e in 
  ensure_ty_equal e'.e_ty e.e_ty e (Some e') "check_fun";
  e'

let e_sub_map g = sub_map (check_fun g)

let e_sub_fold g acc e =
  match e.e_node with
  | V _ | Cnst _ -> acc
  | GetPK (_,kp) | GetSK(_,kp) -> g acc kp
  | Perm(_,_,_,e) | H(_,e) | Proj(_, e) | All(_,e) -> g acc e
  | Tuple(es) | App(_, es) | Nary(_, es)-> L.fold_left g acc es

let e_sub_iter g e = 
  match e.e_node with
  | V _ | Cnst _ -> ()
  | GetPK(_,kp) | GetSK(_,kp) -> g kp
  | Perm(_,_,_,e) -> g e 
  | H(_,e) | Proj(_, e) | All(_,e) -> g e
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
    | GetPK(f,kp) ->
       let kp = go ie kp in
       trans (mk_GetPK f kp)
    | GetSK(f,kp) ->
       let kp = go ie kp in
       trans (mk_GetSK f kp)
    | Perm(f,is_inverse,k,e) ->
       let e = go ie e in
       trans (mk_Perm f is_inverse k e)
    | H(f,e) ->
      let e = go ie e in
      trans (mk_H f e)
    | Tuple(es) ->
      let es = L.map (go ie) es in
      trans (mk_Tuple es)
    | All (b,e) ->
      let e = go ie e in
      trans (mk_All b e)      
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
