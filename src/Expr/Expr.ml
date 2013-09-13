open Type
open Util
open IdType

(* ----------------------------------------------------------------------- *)
(** {1 Expressions} *)

type 'a proj_type = 'a gty * 'a gty * 'a gty

type var = Msg | Cipher | Star
 
let hash_var = function Msg -> 1 | Cipher -> 2 | Star -> 3

type 'a gexpr = {
  e_node : 'a gexpr_node;
  e_ty : 'a gty;
  e_tag  : int
}
and 'a gexpr_node =
  | Z
  | V    of var
  | R    of 'a Rsym.gt
  | P    of 'a Psym.gt   * 'a gexpr
  | Pinv of 'a Psym.gt   * 'a gexpr
  | H    of 'a Hsym.gt   * 'a gexpr
  | App  of                'a gexpr list
  | Proj of 'a proj_type * 'a gexpr
  | Xor  of                'a gexpr * 'a gexpr

type expr = internal gexpr
type expr_node = internal gexpr_node

type eexpr = exported gexpr
type eexpr_node = exported gexpr_node

let e_equal : expr -> expr -> bool = (==)
let e_hash e = e.e_tag
let e_compare e1 e2 = e1.e_tag - e2.e_tag

module Hse = Hashcons.Make (struct
  type t = expr

  let equal e1 e2 =
    ty_equal e1.e_ty e2.e_ty &&
    match e1.e_node, e2.e_node with
    | Z, Z       -> true
    | V v1, V v2 -> v1 = v2
    | R v1, R v2 -> Rsym.equal v1 v2
    | P(f1,e1), P(f2,e2) | Pinv(f1,e1), Pinv(f2,e2) ->
        Psym.equal f1 f2 && e_equal e1 e2
    | H(f1,e1), H(f2,e2) ->
        Hsym.equal f1 f2 && e_equal e1 e2
    | Xor(e11, e12), Xor(e21,e22) ->
        e_equal e11 e21 && e_equal e12 e22
    | App le1, App le2 ->
        list_eq_for_all2 e_equal le1 le2
    | Proj ((tyl1,ty1,tyr1),e1), Proj((tyl2,ty2,tyr2),e2) ->
        e_equal e1 e2 &&
        ty_equal tyl1 tyl2 &&
        ty_equal ty1 ty2 &&
        ty_equal tyr1 tyr2
    | _, _ -> false

  let hash_node = function
    | Z -> 0
    | V v -> hash_var v
    | R v -> Rsym.hash v
    | P(f,e) | Pinv(f,e) ->
        Hashcons.combine (Psym.hash f) (e_hash e)
    | H(f,e) ->
        Hashcons.combine (Hsym.hash f) (e_hash e)
    | Xor(e1,e2) ->
        Hashcons.combine (e_hash e1) (e_hash e2)
    | App le ->
        Hashcons.combine_list e_hash 3 le
    | Proj((tyl,ty,tyr),e) ->
        let h = Hashcons.combine (e_hash e) (ty_hash ty) in
        let h = Hashcons.combine h (ty_hash tyl) in
        Hashcons.combine h (ty_hash tyr)

  let hash e =
    Hashcons.combine (ty_hash e.e_ty) (hash_node e.e_node)

  let tag n e = { e with e_tag = n }
end)

let mk_e n ty = Hse.hashcons {
  e_node = n;
  e_ty   = ty;
  e_tag  = (-1)
}

let mk_ee n ty = {
  e_node = n;
  e_ty   = ty;
  e_tag  = (-1)
}

let rec e_export e =
  let ty = ty_export e.e_ty in
  let e = match e.e_node with
    | Z         -> Z
    | V v       -> V v
    | R v       -> R (Rsym.export v)
    | P(f,a)    -> P(Psym.export f, e_export a)
    | Pinv(f,a) -> Pinv(Psym.export f,e_export a)
    | H(h,a)    -> H(Hsym.export h,e_export a)
    | Xor(a,b)  -> Xor(e_export a, e_export b)
    | App es    -> App(List.map e_export es)
    | Proj((tyl,ty,tyr),a) ->
        let tyl', ty', tyr' = ty_export tyl, ty_export ty, ty_export tyr in
        Proj((tyl',ty',tyr'),e_export a)
  in mk_ee e ty

module E = StructMake (struct
  type t = expr
  let tag = e_hash
end)

module Me = E.M
module Se = E.S
module He = E.H

(* ----------------------------------------------------------------------- *)
(** {2 Indicator functions} *)

let is_Z e = match e.e_node with Z -> true | _ -> false

let is_V e      = match e.e_node with V _ -> true      | _ -> false
let is_Msg e    = match e.e_node with V Msg -> true    | _ -> false
let is_Cipher e = match e.e_node with V Cipher -> true | _ -> false
let is_Star   e = match e.e_node with V Star -> true   | _ -> false

let is_R e = match e.e_node with R _ -> true | _ -> false

let is_P e = match e.e_node with P _ -> true | _ -> false

let is_Pinv e = match e.e_node with Pinv _ -> true | _ -> false

let is_H e = match e.e_node with H _ -> true | _ -> false

let is_Xor e = match e.e_node with Xor _ -> true | _ -> false

let is_App e = match e.e_node with App _ -> true | _ -> false

let is_Proj e = match e.e_node with Proj _ -> true | _ -> false

(* ----------------------------------------------------------------------- *)
(** {3 Destructor functions} *)

exception Destr_failure of string

let destr_V e = match e.e_node with V v -> v | _ -> raise (Destr_failure "V")

let destr_R e = match e.e_node with R v -> v | _ -> raise (Destr_failure "R")

let destr_P e = match e.e_node with P(f,e) -> (f,e) | _ -> raise (Destr_failure "P")

let destr_Pinv e = match e.e_node with Pinv(f,e) -> (f,e) | _ -> raise (Destr_failure "Pinv")

let destr_H e = match e.e_node with H(h,e) -> (h,e) | _ -> raise (Destr_failure "H")

let destr_Xor e = match e.e_node with Xor(e,e') -> (e,e') | _ -> raise (Destr_failure "Xor")

let destr_App e = match e.e_node with App(es) -> es | _ -> raise (Destr_failure "Xor")

let destr_Proj e = match e.e_node with Proj(pt,e) -> (pt,e) | _ -> raise (Destr_failure "Proj")

(* ----------------------------------------------------------------------- *)
(** {4 Pretty printing} *)

let pp_var fmt v =
  Format.fprintf fmt (match v with Msg -> "m_b" | Cipher -> "c_i" | Star -> "*")

let rec pp_exp fmt e =
  match e.e_node with
  | Z when List.length e.e_ty.ty_sum = 1 -> Format.fprintf fmt "0^%a" pp_ty e.e_ty
  | Z -> Format.fprintf fmt "0^{%a}" pp_ty e.e_ty
  | V v -> pp_var fmt v
  | R v -> Rsym.pp fmt v
  | P(f, e) -> Format.fprintf fmt "%a(%a)" Psym.pp f pp_exp e
  | Pinv(f, e) -> Format.fprintf fmt "%a^-1(%a)" Psym.pp f pp_exp e
  | H(f,e) -> Format.fprintf fmt "%a(%a)" Hsym.pp f pp_exp e
  | Xor(e1,e2) -> Format.fprintf fmt "%a + %a" pp_b_exp e1 pp_b_exp e2
  | App l -> Format.fprintf fmt "@[%a@]" (pp_list " |@, " pp_b_exp) l 
  | Proj((tyl,ty,_tyr),e) -> 
      Format.fprintf fmt "[%a]{%a,%a}" pp_exp e pp_ty tyl pp_ty ty
and pp_b_exp fmt e = 
  match e.e_node with
  | App _ | Xor _ ->
      Format.fprintf fmt "(%a)" pp_exp e
  | _ -> pp_exp fmt e

(* ----------------------------------------------------------------------- *)
(** {5 Constructor functions} *)

(** We use a functor so that we don't have to duplicate code for
    hashconsed/internal expressions and external expressions. *)

module type GexprBuild = sig
  type t
  val mk : t gexpr_node -> t gty -> t gexpr
  val ty_equal : t gty -> t gty -> bool
  val ty_concat_l : (t gty) list -> t gty
end

module ExprBuild : GexprBuild with type t = internal = struct
  type t = internal
  let mk = mk_e
  let ty_equal = Type.ty_equal
  let ty_concat_l = Type.ty_concat_l
end

module EexprBuild : GexprBuild with type t = exported = struct
  type t = exported
  let mk = mk_ee
  let ty_equal = (=)
  let ty_concat_l tys =
    mk_ety (List.concat (List.map (fun x -> x.ty_sum) tys))
end

module type S =
sig
  type t
  exception TypeError of (t gty *  t gty * (t gexpr) * (t gexpr) option * string)
  val ensure_ty_equal : t gty -> t gty -> t gexpr -> t gexpr option -> string -> unit
  val mk_Z : t gty -> t gexpr
  val mk_V : var -> t gty -> t gexpr
  val mk_Msg : t gty -> t gexpr
  val mk_Cipher : t gty -> t gexpr
  val mk_Star : t gty -> t gexpr
  val mk_R : t Rsym.gt -> t gexpr
  val mk_P : t Psym.gt -> t gexpr -> t gexpr
  val mk_Pinv : t Psym.gt -> t gexpr -> t gexpr
  val mk_H : t Hsym.gt -> t gexpr -> t gexpr
  val mk_App : (t gexpr) list -> t gexpr
  val mk_Proj : t gty *  t gty * t gty -> t gexpr -> t gexpr
  val mk_Xor : t gexpr -> t gexpr ->  t gexpr
end

module Make (E : GexprBuild) : S with type t = E.t =
struct
  type t = E.t

  exception TypeError of (E.t gty * E.t gty * E.t gexpr * E.t gexpr option * string)

  let ensure_ty_equal ty1 ty2 e1 e2 s =
    ignore (E.ty_equal ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

  let mk_Z ty = E.mk Z ty
  
  let mk_V v ty = E.mk (V v) ty

  let mk_Msg    = mk_V Msg
  let mk_Cipher = mk_V Cipher
  let mk_Star   = mk_V Star
  
  let mk_R v = E.mk (R v) v.Rsym.ty
  
  let mk_P f e =
    ensure_ty_equal e.e_ty f.Psym.dom e None "mk_P";
    E.mk (P(f,e)) f.Psym.dom
  
  let mk_Pinv f e =
    ensure_ty_equal e.e_ty f.Psym.dom e None "mk_Pinv";
    E.mk (Pinv(f,e)) f.Psym.dom

  let mk_H h e =
    ensure_ty_equal e.e_ty h.Hsym.dom e None "mk_H";
    E.mk (H(h,e)) h.Hsym.codom
  
  let mk_App es = E.mk (App(es)) (E.ty_concat_l (List.map (fun e -> e.e_ty) es))
  
  let mk_Proj (tyl,ty,tyr) e =
    ensure_ty_equal e.e_ty (E.ty_concat_l [tyl;ty;tyr]) e None "mk_Proj";
    E.mk (Proj((tyl,ty,tyr),e)) ty
  
  let mk_Xor a b =
    ensure_ty_equal a.e_ty b.e_ty a (Some b) "mk_Xor";
    E.mk (Xor(a,b)) a.e_ty
end

module Constructors : S with type t = internal = Make(ExprBuild) 
module EConstructors : S with type t = exported = Make(EexprBuild)

include Constructors

let mk_Proj2 (tyl,ty) e =
  match ty_minus e.e_ty (ty_concat tyl ty) with
  | Some tyr -> mk_Proj (tyl,ty,tyr) e
  | None     -> raise (TypeError(e.e_ty,ty_concat tyl ty,e,None,"mk_Proj2"))


(* ----------------------------------------------------------------------- *)
(** {6 Generic functions on [expr]} *)

let sub_map g e = 
  match e.e_node with
  | Z | V _ | R _ -> e
  | P(f, e1) -> 
      let e1' = g e1 in
      if e1 == e1' then e
      else mk_e (P(f,e1')) e.e_ty
  | Pinv(f, e1) -> 
      let e1' = g e1 in
      if e1 == e1' then e
      else mk_e (Pinv(f,e1')) e.e_ty
  | H(h,e1) ->
      let e1' = g e1 in
      if e1 == e1' then e
      else mk_e (H(h,e1')) e.e_ty
  | App l -> 
      let l' = smart_map g l in
      if l == l' then e
      else mk_e (App l') e.e_ty
  | Proj(ty,e1) ->
       let e1' = g e1 in
       if e1 == e1' then e
       else mk_e (Proj(ty,e1')) e.e_ty
  | Xor(e1,e2) ->
      let e1' = g e1 in
      let e2' = g e2 in
      if e1 == e1' && e2 == e2' then e
      else mk_e (Xor(e1', e2')) e.e_ty 

let check_fun g e =
  let e' = g e in 
  ensure_ty_equal e'.e_ty e.e_ty e (Some e') "check_fun";
  e'

let e_sub_map g = sub_map (check_fun g)

let e_sub_fold g acc e = 
  match e.e_node with
  | Z | V _ | R _ -> acc
  | P(_,e) | Pinv(_,e) | H(_,e) | Proj(_,e) -> g acc e 
  | Xor(e1,e2) -> g (g acc e1) e2
  | App l -> List.fold_left g acc l

let e_sub_iter g e = 
  match e.e_node with
  | Z | V _ | R _ -> ()
  | P(_,e) | Pinv(_,e) | H(_,e) | Proj(_,e) -> g e 
  | Xor(e1,e2) -> g e1; g e2
  | App l -> List.iter g l

let rec e_iter g e =
  g e; e_sub_iter (e_iter g) e

let e_sub_exists f e = 
  match e.e_node with
  | P(_,e) | Pinv(_,e) | H(_,e) | Proj(_,e) -> f e
  | Xor(e1,e2) -> f e1 || f e2
  | App l -> List.exists f l
  | _ -> false

let rec e_exists f e =
  f e || e_sub_exists (e_exists f) e

let e_sub_forall f e = 
  match e.e_node with
  | P(_,e) | Pinv(_,e) | H(_,e) | Proj(_,e) -> f e
  | Xor(e1,e2) -> f e1 && f e2
  | App l -> List.for_all f l
  | _ -> true

let rec e_forall f e = 
  f e && e_sub_forall (e_forall f) e

let e_find (type t) f (e : t gexpr) = 
  let module E = struct exception Found of (t gexpr) end in
  let rec aux e = 
    if f e then raise (E.Found e)
    else e_sub_iter aux e in
  try aux e; raise Not_found with E.Found e -> e

let e_find_all f e =
  let rec aux s e =
    let s = if f e then Se.add e s else s in
    e_sub_fold aux s e in
  aux Se.empty e

let e_rvars = e_find_all is_R

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

let e_map_top f = 
  let tbl = He.create 103 in
  let rec aux e = 
    try He.find tbl e 
    with _ ->
      let e' = try check_fun f e with Not_found -> sub_map aux e in
      He.add tbl e e';
      e' in
  aux 

let e_replace e1 e2 = 
  e_map_top (fun e -> if e_equal e e1 then e2 else raise Not_found)

let e_subst s = e_map_top (fun e -> Me.find e s)


