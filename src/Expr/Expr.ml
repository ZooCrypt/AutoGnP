open Type
open Util
open IdType

(* ----------------------------------------------------------------------- *)
(** {1 Expressions} *)

type 'a proj_type = 'a gty * 'a gty * 'a gty

(* constants *)
type cnst =
    GGen
  | FZ
  | Z
  | FOne

let cnst_hash = function
    GGen -> 1
  | FZ   -> 2
  | Z    -> 3
  | FOne -> 4

(* operators with fixed arity *)
type op =
    GExp   (* exponentiation in source group *)
  | GLog   (* discrete logarithm in source group *)
  | EMap   (* bilinear map *)
  | GTExp  (* exponentiation in target group *)
  | GTLog  (* discrete logarithm in target group *)
  | FOpp   (* additive inverse in Fq *)
  | FMinus (* subtraction in Fq *)
  | FInv   (* mult. inverse in Fq *)
  | FDiv   (* division in Fq *)
  | Eq     (* equality *)
  | Ifte   (* if then else *)

let op_hash = function
    GExp   -> 1
  | GLog   -> 2
  | EMap   -> 3
  | GTExp  -> 4
  | GTLog  -> 5
  | FOpp   -> 6
  | FMinus -> 7
  | FInv   -> 8
  | FDiv   -> 9
  | Eq     -> 10
  | Ifte   -> 11

(* associative operators with variable arity *)
type naryop =
    GMult
  | GTMult
  | FPlus
  | FMult
  | Xor
  | Land   (* logical and *)

let naryop_hash = function
    GMult  -> 1
  | GTMult -> 2
  | FPlus  -> 3
  | FMult  -> 4
  | Xor    -> 5
  | Land   -> 6

type 'a gexpr = {
  e_node : 'a gexpr_node;
  e_ty : 'a gty;
  e_tag  : int
}
and 'a gexpr_node =
  | V    of 'a Vsym.gt
  | H    of 'a Hsym.gt * 'a gexpr
  | Tuple of ('a gexpr) list
  | Proj  of int * 'a gexpr
  | Cnst of cnst
  | App  of op     * 'a gexpr list
  | Nary of naryop * 'a gexpr list
  | ElemH of 'a gexpr * 'a Hsym.gt


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
    | V v1, V v2                 -> Vsym.equal v1 v2
    | H(f1,e1), H(f2,e2)         -> Hsym.equal f1 f2 && e_equal e1 e2
    | Tuple es1, Tuple es2       -> list_eq_for_all2 e_equal es1 es2
    | Proj(i1, e1), Proj(i2, e2) -> i1 = i2 && e_equal e1 e2
    | Cnst c1, Cnst c2           -> c1 = c2
    | App(o1,es1), App(o2, es2)  -> o1 = o2 && list_eq_for_all2 e_equal es1 es2
    | Nary(o1,es1), Nary(o2,es2) -> o1 = o2 && list_eq_for_all2 e_equal es1 es2
    | ElemH(e1,h1), ElemH(e2,h2) -> e_equal e1 e2 && Hsym.equal h1 h2
    | _, _                       -> false

  let hash_node = function
    | V(v)       -> Vsym.hash v
    | H(f,e)     -> Hashcons.combine (Hsym.hash f) (e_hash e)
    | Tuple(es)  -> Hashcons.combine_list e_hash 3 es
    | Proj(i,e)  -> Hashcons.combine i (e_hash e)
    | Cnst(c)    -> cnst_hash c
    | App(o,es)  -> Hashcons.combine_list e_hash (op_hash o) es
    | Nary(o,es) -> Hashcons.combine_list e_hash (naryop_hash o) es
    | ElemH(e,h) -> Hashcons.combine (Hsym.hash h)  (e_hash e)

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
    | V(v)       -> V(Vsym.export v)
    | H(f,e)     -> H(Hsym.export f, e_export e)
    | Tuple(es)  -> Tuple(List.map e_export es)
    | Proj(i,e)  -> Proj(i,e_export e)
    | Cnst(c)    -> Cnst(c)
    | App(o,es)  -> App(o, List.map e_export es)
    | Nary(o,es) -> Nary(o, List.map e_export es)
    | ElemH(e,h) -> ElemH(e_export e, Hsym.export h)
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

let is_V e = match e.e_node with V _ -> true | _ -> false

let is_H e = match e.e_node with H _ -> true | _ -> false

let is_Tuple e = match e.e_node with Tuple _ -> true | _ ->  false

let is_Proj e = match e.e_node with Proj _ -> true | _ ->  false

let is_some_Cnst e = match e.e_node with Cnst _ -> true | _ -> false

let is_Cnst c e = match e.e_node with Cnst c' -> c = c' | _ -> false

let is_some_App e = match e.e_node with App _ -> true | _ -> false

let is_App o e = match e.e_node with App(o',_) -> o = o' | _ -> false

let is_some_Nary e = match e.e_node with Nary _ -> true | _ -> false

let is_Nary o e = match e.e_node with Nary(o',_) -> o' = o | _ -> false

let is_ElemH e = match e.e_node with ElemH _ -> true | _ -> false

(* ----------------------------------------------------------------------- *)
(** {3 Destructor functions} *)

exception Destr_failure of string

(*
    V    of 'a Vsym.gt
  | H    of 'a Hsym.gt * 'a gexpr
  | Tuple of ('a gexpr) list
  | Proj  of int * 'a gexpr
  | Cnst of cnst
      GGen
    | FZ
    | Z 
    | FOne
  | App  of op     * 'a gexpr list
      GExp
    | GLog
    | EMap
    | GTExp
    | GTLog
    | FOpp
    | FMinus
    | FInv
    | FDiv
    | Eq
    | Ifte
  | Nary of naryop * 'a gexpr list
      GMult
    | GTMult
    | FPlus
    | FMult
    | Xor
    | Land
  | ElemH of 'a gexpr * 'a Hsym.gt
*)


let destr_V e = match e.e_node with V v -> v | _ -> raise (Destr_failure "V")

let destr_H e = match e.e_node with H(h,e) -> (h,e) | _ -> raise (Destr_failure "H")

let destr_Tuple e = match e.e_node with Tuple(es) -> (es) | _ -> raise (Destr_failure "Tuple")

let destr_Proj e = match e.e_node with Proj(i,e) -> (i,e) | _ -> raise (Destr_failure "Proj")

let destr_Cnst e = match e.e_node with Cnst(c) -> (c) | _ -> raise (Destr_failure "Cnst")

let destr_App e = match e.e_node with App(o,es) -> (o,es) | _ -> raise (Destr_failure "App")

let destr_GExp e = match e.e_node with App(GExp,[a;b]) -> (a,b) | _ -> raise (Destr_failure "GExp")

let destr_GLog e = match e.e_node with App(GLog,[a]) -> a | _ -> raise (Destr_failure "GLog")

let destr_GTExp e = match e.e_node with App(GTExp,[a;b]) -> (a,b) | _ -> raise (Destr_failure "GTExp")

let destr_GTLog e = match e.e_node with App(GTLog,[a]) -> a | _ -> raise (Destr_failure "GTLog")

let destr_FOpp e = match e.e_node with App(FOpp,[a]) -> a | _ -> raise (Destr_failure "FOpp")

let destr_FMinus e = match e.e_node with App(FMinus,[a;b]) -> (a,b) | _ -> raise (Destr_failure "FMinus")

let destr_FInv e = match e.e_node with App(FInv,[a]) -> a | _ -> raise (Destr_failure "FInv")

let destr_FDiv e = match e.e_node with App(FDiv,[a;b]) -> (a,b) | _ -> raise (Destr_failure "FDiv")

let destr_Eq e = match e.e_node with App(Eq,[a;b]) -> (a,b) | _ -> raise (Destr_failure "Eq")

let destr_Ifte e = match e.e_node with App(Eq,[a;b;c]) -> (a,b,c) | _ -> raise (Destr_failure "Ifte")

let destr_GMult e = match e.e_node with Nary(GMult,e::es) -> e::es | _ -> raise (Destr_failure "GMult")

let destr_GTMult e = match e.e_node with Nary(GTMult,e::es) -> e::es | _ -> raise (Destr_failure "GTMult")

let destr_FPlus e = match e.e_node with Nary(FPlus,e::es) -> e::es | _ -> raise (Destr_failure "FPlus")

let destr_FMult e = match e.e_node with Nary(FMult,e::es) -> e::es | _ -> raise (Destr_failure "FMult")

let destr_Xor e = match e.e_node with Nary(Xor,e::es) -> e::es | _ -> raise (Destr_failure "Xor")

let destr_Land e = match e.e_node with Nary(Land,e::es) -> e::es | _ -> raise (Destr_failure "Land")

(* ----------------------------------------------------------------------- *)
(** {4 Pretty printing} *)

let pp_cnst fmt c ty =
  match c with
  | GGen -> Format.fprintf fmt "g"
  | FZ   -> Format.fprintf fmt "0%%Fq"
  | Z    -> Format.fprintf fmt "0%%%a" pp_ty ty
  | FOne -> Format.fprintf fmt "1%%Fq"

let pp_nop : (naryop -> string) = function
    GMult  -> "x"
  | GTMult -> "x"
  | FPlus  -> "+"
  | FMult  -> "*"
  | Xor    -> "(+)"
  | Land   -> "/\\"

let rec pp_exp fmt e =
  match e.e_node with
  | V(v)       -> Vsym.pp fmt v
  | H(h,e)     -> Format.fprintf fmt "%a(%a)" Hsym.pp h pp_exp e
  | Tuple(es)  -> Format.fprintf fmt "(%a)" (pp_list "," pp_exp) es
  | Proj(i,e)  -> Format.fprintf fmt "pi_%i(%a)" i pp_exp e
  | Cnst(c)    -> pp_cnst fmt c e.e_ty
  | App(o,es)  -> pp_op fmt o es
  | Nary(o,es) -> Format.fprintf fmt "(%a)" (pp_list (pp_nop o) pp_exp) es (* FIXME: handle prios *)
  | ElemH(e,h) -> Format.fprintf fmt "%a in L_%a" pp_exp e Hsym.pp h
and pp_op fmt o es = 
  match o, es with
  | GExp, [a;b]   -> Format.fprintf fmt "%a^%a" pp_exp a pp_exp b
  | GLog, [a]     -> Format.fprintf fmt "log(%a)" pp_exp a
  | EMap, [a;b]   -> Format.fprintf fmt "e(%a,%a)" pp_exp a pp_exp b
  | GTExp, [a;b]  -> Format.fprintf fmt "%a^%a" pp_exp a pp_exp b
  | GTLog, [a]    -> Format.fprintf fmt "log(%a)" pp_exp a
  | FOpp, [a]     -> Format.fprintf fmt "-%a" pp_exp a
  | FMinus, [a;b] -> Format.fprintf fmt "%a - %a" pp_exp a pp_exp b
  | FInv, [a]     -> Format.fprintf fmt "%a^-1" pp_exp a
  | FDiv, [a;b]   -> Format.fprintf fmt "%a / %a" pp_exp a pp_exp b
  | Eq, [a;b]     -> Format.fprintf fmt "%a = %a" pp_exp a pp_exp b
  | Ifte, [a;b;c] -> Format.fprintf fmt "%a ? %a : %a" pp_exp a pp_exp b pp_exp c
  | _             -> failwith "pp_op: invalid expression"


(* ----------------------------------------------------------------------- *)
(** {5 Constructor functions} *)

(** We use a functor so that we don't have to duplicate code for
    hashconsed/internal expressions and external expressions. *)

module type GexprBuild = sig
  type t
  val mk : t gexpr_node -> t gty -> t gexpr
  val ty_equal : t gty -> t gty -> bool
end

module ExprBuild : GexprBuild with type t = internal = struct
  type t = internal
  let mk = mk_e
  let ty_equal = Type.ty_equal
end

module EexprBuild : GexprBuild with type t = exported = struct
  type t = exported
  let mk = mk_ee
  let ty_equal = (=)
end

(*
module type S =
sig
  type t
  exception TypeError of (t gty *  t gty * (t gexpr) * (t gexpr) option * string)
  val ensure_ty_equal : t gty -> t gty -> t gexpr -> t gexpr option -> string -> unit
  val mk_Z : t gty -> t gexpr
  val mk_V : t Vsym.gt -> t gexpr
  val mk_H : t Hsym.gt -> t gexpr -> t gexpr
  val mk_Xor : t gexpr -> t gexpr ->  t gexpr
end

module Make (E : GexprBuild) : S with type t = E.t =
struct
  type t = E.t

  exception TypeError of (E.t gty * E.t gty * E.t gexpr * E.t gexpr option * string)

  let ensure_ty_equal ty1 ty2 e1 e2 s =
    ignore (E.ty_equal ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

  let mk_Z ty = E.mk Z ty
  
  let mk_V v = E.mk (V v) v.Vsym.ty
  
  let mk_H h e =
    ensure_ty_equal e.e_ty h.Hsym.dom e None "mk_H";
    E.mk (H(h,e)) h.Hsym.codom
  
  let mk_Xor a b =
    ensure_ty_equal a.e_ty b.e_ty a (Some b) "mk_Xor";
    E.mk (Xor(a,b)) a.e_ty
end

module Constructors : S with type t = internal = Make(ExprBuild) 
module EConstructors : S with type t = exported = Make(EexprBuild)

include Constructors

(* ----------------------------------------------------------------------- *)
(** {6 Generic functions on [expr]} *)

let sub_map g e = 
  match e.e_node with
  | Z | V _ -> e
  | H(h,e1) ->
      let e1' = g e1 in
      if e1 == e1' then e
      else mk_e (H(h,e1')) e.e_ty
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
  | Z | V _ -> acc
  | H(_,e) -> g acc e 
  | Xor(e1,e2) -> g (g acc e1) e2

let e_sub_iter g e = 
  match e.e_node with
  | Z | V _ -> ()
  | H(_,e) -> g e 
  | Xor(e1,e2) -> g e1; g e2

let rec e_iter g e =
  g e; e_sub_iter (e_iter g) e

let e_sub_exists f e = 
  match e.e_node with
  | H(_,e) -> f e
  | Xor(e1,e2) -> f e1 || f e2
  | _ -> false

let rec e_exists f e =
  f e || e_sub_exists (e_exists f) e

let e_sub_forall f e = 
  match e.e_node with
  | H(_,e) -> f e
  | Xor(e1,e2) -> f e1 && f e2
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

let e_vars = e_find_all is_V

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

*)