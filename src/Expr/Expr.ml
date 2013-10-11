open Type
open Util
open IdType

module F = Format

(* ----------------------------------------------------------------------- *)
(** {1 Expressions} *)

type 'a proj_type = 'a gty * 'a gty * 'a gty

(* constants *)
type cnst =
    GGen (* generator of G *)
  | FZ   (* 0 in Fq *)
  | Z    (* 0 bitstring *)
  | FOne (* 1 in Fq *)
  | B  of bool

let cnst_hash = function
  | GGen -> 1
  | FZ   -> 2
  | Z    -> 3
  | FOne -> 4
  | B b  -> if b then 5 else 6

(* operators with fixed arity *)
type op =
    GMult  (* multiplication in G *)
  | GExp   (* exponentiation in source group *)
  | GLog   (* discrete logarithm in source group *)
  | EMap   (* bilinear map *)
  | GTMult (* multiplication in GT *)
  | GTExp  (* exponentiation in target group *)
  | GTLog  (* discrete logarithm in target group *)
  | FOpp   (* additive inverse in Fq *)
  | FMinus (* subtraction in Fq *)
  | FInv   (* mult. inverse in Fq *)
  | FDiv   (* division in Fq *)
  | Eq     (* equality *)
  | Not    (* negation *)
  | Ifte   (* if then else *)

let op_hash = function
    GMult  -> 1
  | GExp   -> 2
  | GLog   -> 3
  | EMap   -> 4
  | GTMult -> 5
  | GTExp  -> 6
  | GTLog  -> 7
  | FOpp   -> 8
  | FMinus -> 9
  | FInv   -> 10
  | FDiv   -> 11
  | Eq     -> 12
  | Not    -> 14
  | Ifte   -> 13

(* associative operators with variable arity *)
type naryop =
    FPlus  (* plus in Fq *)
  | FMult  (* multiplication in Fq *)
  | Xor    (* Xor of bitstrings *)
  | Land   (* logical and *)

let naryop_hash = function
    FPlus  -> 3
  | FMult  -> 4
  | Xor    -> 5
  | Land   -> 6

type 'a gexpr = {
  e_node : 'a gexpr_node;
  e_ty : 'a gty;
  e_tag  : int
}
and 'a gexpr_node =
  | V    of 'a Vsym.gt             (* variables (program, logical, random, ...) *)
  | H    of 'a Hsym.gt * 'a gexpr  (* hash function application *)
  | Tuple of ('a gexpr) list       (* tuples *)
  | Proj  of int * 'a gexpr        (* projection *)
  | Cnst of cnst                   (* constants *)
  | App  of op     * 'a gexpr list (* fixed arity operators *)
  | Nary of naryop * 'a gexpr list (* variable arity AC operators *)
  | ElemH of 'a gexpr * 'a Hsym.gt (* ElemH(e,h): e in L_H *)


type expr = internal gexpr
type expr_node = internal gexpr_node

type eexpr = exported gexpr
type eexpr_node = exported gexpr_node

let e_equal : expr -> expr -> bool = (==)
let e_hash (e:expr) = e.e_tag
let e_compare (e1:expr) (e2:expr) = e1.e_tag - e2.e_tag

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

let is_True e = is_Cnst (B true) e

let is_False e = is_Cnst (B false) e

let is_GGen e = is_Cnst GGen e

let is_GTGen e = 
  match e.e_node with
  | App(EMap, [e1;e2]) -> is_GGen e1 && is_GGen e2
  | _ -> false

let is_some_App e = match e.e_node with App _ -> true | _ -> false

let is_App o e = match e.e_node with App(o',_) -> o = o' | _ -> false

let is_some_Nary e = match e.e_node with Nary _ -> true | _ -> false

let is_Nary o e = match e.e_node with Nary(o',_) -> o' = o | _ -> false

let is_ElemH e = match e.e_node with ElemH _ -> true | _ -> false

let is_GLog e = is_App GLog e
let is_GTLog e = is_App GTLog e

(* ----------------------------------------------------------------------- *)
(** {3 Destructor functions} *)

exception Destr_failure of string

let destr_V e = match e.e_node with V v -> v | _ -> raise (Destr_failure "V")

let destr_H e = match e.e_node with H(h,e) -> (h,e) | _ -> raise (Destr_failure "H")

let destr_Tuple e = match e.e_node with Tuple(es) -> (es) | _ -> raise (Destr_failure "Tuple")

let destr_Proj e = match e.e_node with Proj(i,e) -> (i,e) | _ -> raise (Destr_failure "Proj")

let destr_Cnst e = match e.e_node with Cnst(c) -> (c) | _ -> raise (Destr_failure "Cnst")

let destr_App e = match e.e_node with App(o,es) -> (o,es) | _ -> raise (Destr_failure "App")

let destr_GMult e = match e.e_node with App(GMult,[a;b]) -> (a,b) | _ -> raise (Destr_failure "GMult")

let destr_GExp e = match e.e_node with App(GExp,[a;b]) -> (a,b) | _ -> raise (Destr_failure "GExp")

let destr_GLog e = match e.e_node with App(GLog,[a]) -> a | _ -> raise (Destr_failure "GLog")

let destr_GTMult e = match e.e_node with App(GTMult,[a;b]) -> (a,b) | _ -> raise (Destr_failure "GTMult")

let destr_GTExp e = match e.e_node with App(GTExp,[a;b]) -> (a,b) | _ -> raise (Destr_failure "GTExp")

let destr_GTLog e = match e.e_node with App(GTLog,[a]) -> a | _ -> raise (Destr_failure "GTLog")

let destr_FOpp e = match e.e_node with App(FOpp,[a]) -> a | _ -> raise (Destr_failure "FOpp")

let destr_FMinus e = match e.e_node with App(FMinus,[a;b]) -> (a,b) | _ -> raise (Destr_failure "FMinus")

let destr_FInv e = match e.e_node with App(FInv,[a]) -> a | _ -> raise (Destr_failure "FInv")

let destr_FDiv e = match e.e_node with App(FDiv,[a;b]) -> (a,b) | _ -> raise (Destr_failure "FDiv")

let destr_Eq e = match e.e_node with App(Eq,[a;b]) -> (a,b) | _ -> raise (Destr_failure "Eq")

let destr_Not e = match e.e_node with App(Not,[a]) -> a | _ -> raise (Destr_failure "FDiv")

let destr_Ifte e = match e.e_node with App(Eq,[a;b;c]) -> (a,b,c) | _ -> raise (Destr_failure "Ifte")

let destr_FPlus e = match e.e_node with Nary(FPlus,e::es) -> e::es | _ -> raise (Destr_failure "FPlus")

let destr_FMult e = match e.e_node with Nary(FMult,e::es) -> e::es | _ -> raise (Destr_failure "FMult")

let destr_Xor e = match e.e_node with Nary(Xor,e::es) -> e::es | _ -> raise (Destr_failure "Xor")

let destr_Land e = match e.e_node with Nary(Land,e::es) -> e::es | _ -> raise (Destr_failure "Land")

(* ----------------------------------------------------------------------- *)
(** {4 Pretty printing} *)

let pp_cnst fmt c ty =
  match c with
  | GGen -> F.fprintf fmt "g"
  | FZ   -> F.fprintf fmt "0"
  | Z    -> F.fprintf fmt "0%%%a" pp_ty ty
  | FOne -> F.fprintf fmt "1"
  | B b  -> F.fprintf fmt "%b" b

let rec pp_exp fmt e =
  match e.e_node with
  | V(v)       -> Vsym.pp fmt v
  | H(h,e)     -> F.fprintf fmt "%a(%a)" Hsym.pp h pp_exp e
  | Tuple(es)  -> F.fprintf fmt "(%a)" (pp_list ", " pp_exp) es
  | Proj(i,e)  -> F.fprintf fmt "pi_%i(%a)" i pp_exp e
  | Cnst(c)    -> pp_cnst fmt c e.e_ty
  | App(o,es)  -> pp_op fmt o es
  | Nary(o,es) -> F.fprintf fmt "(%a)"  pp_nop (o,es)
  | ElemH(e,h) -> F.fprintf fmt "%a in L_%a" pp_exp e Hsym.pp h
and pp_op fmt o es = 
  match o, es with
  | GMult, [a;b]  -> F.fprintf fmt "(%a x %a)" pp_exp a pp_exp b
  | GExp, [a;b]   -> F.fprintf fmt "%a^%a" pp_exp a pp_exp b
  | GLog, [a]     -> F.fprintf fmt "log(%a)" pp_exp a
  | EMap, [a;b]   -> F.fprintf fmt "e(%a,%a)" pp_exp a pp_exp b
  | GTMult, [a;b] -> F.fprintf fmt "(%a x %a)" pp_exp a pp_exp b
  | GTExp, [a;b]  -> F.fprintf fmt "%a^%a" pp_exp a pp_exp b
  | GTLog, [a]    -> F.fprintf fmt "log(%a)" pp_exp a
  | FOpp, [a]     -> F.fprintf fmt "-%a" pp_exp a
  | FMinus, [a;b] -> F.fprintf fmt "%a - %a" pp_exp a pp_exp b
  | FInv, [a]     -> F.fprintf fmt "%a^-1" pp_exp a
  | FDiv, [a;b]   -> F.fprintf fmt "%a / %a" pp_exp a pp_exp b
  | Eq, [a;b]     -> F.fprintf fmt "%a = %a" pp_exp a pp_exp b
  | Ifte, [a;b;c] -> F.fprintf fmt "%a ? %a : %a" pp_exp a pp_exp b pp_exp c
  | Not, [a]      -> F.fprintf fmt "not (%a)" pp_exp a
  | _             -> failwith "pp_op: invalid expression"
and pp_nop fmt (o,es) = match o with
    FPlus  -> pp_list " + " pp_exp fmt es
  | FMult  -> pp_list " * " pp_exp fmt es
  | Xor    -> pp_list " (+) " pp_exp fmt es
  | Land   -> pp_list " /\\ " pp_exp fmt es

(* ----------------------------------------------------------------------- *)
(** {5 Constructor functions} *)

(** We use a functor so that we don't have to duplicate code for
    hashconsed/internal expressions and external expressions. *)

module type GexprBuild = sig
  type t
  val mk : t gexpr_node -> t gty -> t gexpr
  val ty_equal : t gty -> t gty -> bool
  val mk_ty : t gty_node -> t gty
end

module ExprBuild : GexprBuild with type t = internal = struct
  type t = internal
  let mk = mk_e
  let ty_equal = Type.ty_equal
  let mk_ty =  mk_ty
end

module EexprBuild : GexprBuild with type t = exported = struct
  type t = exported
  let mk = mk_ee
  let ty_equal = (=)
  let mk_ty = mk_ety
end

module type S =
sig
  type t
  exception TypeError of (t gty *  t gty * (t gexpr) * (t gexpr) option * string)
  val ensure_ty_equal : t gty -> t gty -> t gexpr -> t gexpr option -> string -> unit
  val mk_V : t Vsym.gt -> t gexpr
  val mk_H : t Hsym.gt -> t gexpr -> t gexpr
  val mk_Tuple : (t gexpr) list -> t gexpr
  val mk_Proj : int -> t gexpr -> t gexpr
  val mk_ElemH : t gexpr -> t Hsym.gt -> t gexpr
  
  val mk_GGen  : t gexpr
  val mk_GTGen : t gexpr
  val mk_FZ    : t gexpr
  val mk_FOne  : t gexpr
  val mk_Z     : t Lenvar.gid -> t gexpr
  val mk_B     : bool -> t gexpr
  val mk_True  : t gexpr
  val mk_False : t gexpr

  val mk_GMult : t gexpr -> t gexpr -> t gexpr
  val mk_GExp : t gexpr -> t gexpr -> t gexpr
  val mk_GLog : t gexpr -> t gexpr
  val mk_EMap : t gexpr -> t gexpr -> t gexpr
  val mk_GTMult : t gexpr -> t gexpr -> t gexpr
  val mk_GTExp : t gexpr -> t gexpr -> t gexpr
  val mk_GTLog : t gexpr -> t gexpr
  val mk_FOpp : t gexpr -> t gexpr
  val mk_FMinus : t gexpr -> t gexpr -> t gexpr
  val mk_FInv : t gexpr -> t gexpr
  val mk_FDiv : t gexpr -> t gexpr -> t gexpr
  val mk_Eq : t gexpr -> t gexpr -> t gexpr
  val mk_Not : t gexpr -> t gexpr  
  val mk_Ifte : t gexpr -> t gexpr -> t gexpr -> t gexpr

  val mk_FPlus : (t gexpr) list -> t gexpr
  val mk_FMult : (t gexpr) list -> t gexpr
  val mk_Xor : (t gexpr) list -> t gexpr
  val mk_Land : (t gexpr) list -> t gexpr
end

module Make (E : GexprBuild) : S with type t = E.t =
struct
  type t = E.t

  exception TypeError of (E.t gty * E.t gty * E.t gexpr * E.t gexpr option * string)

  let ensure_ty_equal ty1 ty2 e1 e2 s =
    ignore (E.ty_equal ty1 ty2 || raise (TypeError(ty1,ty2,e1,e2,s)))

  let ty_G = E.mk_ty G
  let ty_GT = E.mk_ty GT
  let ty_Fq = E.mk_ty Fq
  let ty_Bool = E.mk_ty Bool
  let ty_BS lv = E.mk_ty (BS lv)
  let ty_Prod tys = E.mk_ty (Prod tys)

  let mk_V v = E.mk (V v) v.Vsym.ty
  
  let mk_H h e =
    ensure_ty_equal e.e_ty h.Hsym.dom e None "mk_H";
    E.mk (H(h,e)) h.Hsym.codom

  let mk_Tuple es =
    E.mk (Tuple es) (ty_Prod (List.map (fun e -> e.e_ty) es))

  let mk_Proj i e = match e.e_ty.ty_node with
    | Prod(tys) when i >= 0 && List.length tys < i -> E.mk (Proj(i,e)) (List.nth tys i)
    | _ -> raise (TypeError(e.e_ty, e.e_ty, e, None, "mk_Proj expected product type"))

  let mk_ElemH e h =
    ensure_ty_equal e.e_ty h.Hsym.codom e None "mk_ElemH";
    E.mk (ElemH(e,h)) ty_Bool
  
  let mk_Cnst c ty = E.mk (Cnst c) ty

  let mk_GGen = mk_Cnst GGen ty_G
  let mk_FZ = mk_Cnst FZ ty_Fq
  let mk_FOne = mk_Cnst FOne ty_Fq
  let mk_Z lv = mk_Cnst Z (ty_BS lv)
  let mk_B  b = mk_Cnst (B b) ty_Bool
  let mk_True = mk_B true
  let mk_False = mk_B false


  let mk_App o es ty = E.mk (App(o,es)) ty

  let mk_GMult a b =
    ensure_ty_equal a.e_ty ty_G a None "mk_GMult";
    ensure_ty_equal b.e_ty ty_G b None "mk_GMult";
    mk_App GMult [a;b] ty_G

  let mk_GExp a b =
    ensure_ty_equal a.e_ty ty_G a None "mk_GExp";
    ensure_ty_equal b.e_ty ty_Fq b None "mk_GExp";
    mk_App GExp [a;b] ty_G

  let mk_GLog a =
    ensure_ty_equal a.e_ty ty_G a None "mk_GLog";
    mk_App GLog [a] ty_G

  let mk_EMap a b =
    ensure_ty_equal a.e_ty ty_G a None "mk_EMap";
    ensure_ty_equal b.e_ty ty_G b None "mk_EMap";
    mk_App EMap [a;b] ty_GT

  let mk_GTMult a b =
    ensure_ty_equal a.e_ty ty_GT a None "mk_GTMult";
    ensure_ty_equal b.e_ty ty_GT b None "mk_GTMult";
    mk_App GTMult [a;b] ty_GT

  let mk_GTExp a b =
    ensure_ty_equal a.e_ty ty_GT a None "mk_GTExp";
    ensure_ty_equal b.e_ty ty_Fq b None "mk_GTExp";
    mk_App GTExp [a;b] ty_GT

  let mk_GTLog a =
    ensure_ty_equal a.e_ty ty_GT a None "mk_GTLog";
    mk_App GTLog [a] ty_Fq

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

  let mk_nary s o es ty =
    match es with
    | []  -> failwith (F.sprintf "%s: empty list given" s);
    | [a] -> a
    | _   -> List.iter (fun e -> ensure_ty_equal e.e_ty ty e None s) es;
             E.mk (Nary(o,es)) ty

  let mk_FPlus es = mk_nary "mk_FPlus" FPlus es ty_Fq 
  let mk_FMult es = mk_nary "mk_FMult" FMult es ty_Fq
  let mk_Xor es = match es with
    | e::_ -> (match e.e_ty.ty_node with
               | BS _ -> mk_nary "mk_Xor" Xor es e.e_ty
               | _ -> failwith "mk_Xor: expected bitstring argument")
    | _ -> failwith "mk_Xor: expected non-empty list"
  let mk_Land es = mk_nary "mk_FMult" Land es ty_Bool

  let mk_GTGen = mk_EMap mk_GGen mk_GGen

end

module Constructors : S with type t = internal = Make(ExprBuild) 
module EConstructors : S with type t = exported = Make(EexprBuild)

include Constructors

(* ----------------------------------------------------------------------- *)
(** {6 Generic functions on [expr]} *)

let sub_map g e = 
  match e.e_node with
  | V _ | Cnst _ -> e
  | H(h,e) ->
      let e' = g e in
      if e == e' then e
      else mk_e (H(h,e')) e.e_ty
  | ElemH(e,h) ->
      let e' = g e in
      if e == e' then e
      else mk_e (ElemH(e',h)) e.e_ty
  | Tuple(es) ->
      let es' = smart_map g es in
      if es == es' then e
      else mk_e (Tuple(es')) e.e_ty
  | Proj(i, e) ->
      let e' = g e in
      if e == e' then e
      else mk_e (Proj(i,e')) e.e_ty
  | App(o, es) ->
      let es' = smart_map g es in
      if es == es' then e
      else mk_e (App(o,es')) e.e_ty
  | Nary(o, es) ->
      let es' = smart_map g es in
      if es == es' then e
      else mk_e (Nary(o,es')) e.e_ty

let check_fun g e =
  let e' = g e in 
  ensure_ty_equal e'.e_ty e.e_ty e (Some e') "check_fun";
  e'

let e_sub_map g = sub_map (check_fun g)

let e_sub_fold g acc e =
  match e.e_node with
  | V _ | Cnst _ -> acc
  | H(_,e) | Proj(_, e) | ElemH(e,_) -> g acc e
  | Tuple(es) | App(_, es) | Nary(_, es)-> List.fold_left g acc es

let e_sub_iter g e = 
  match e.e_node with
  | V _ | Cnst _ -> ()
  | H(_,e) | Proj(_, e) | ElemH(e,_) -> g e
  | Tuple(es) | App(_, es) | Nary(_, es)-> List.iter g es

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

type context = (Vsym.t * expr)

let inst_ctxt (v, e') e = e_replace (mk_V v) e e'

let typeError_to_string (ty1,ty2,e1,me2,_s) =
  match me2 with
  | Some e2 -> 
      format_to_string (fun fmt ->
        F.fprintf fmt "incompatible types `%a' vs. `%a' for expressions `%a' and `%a'"
          pp_ty ty1 pp_ty ty2 pp_exp e1 pp_exp e2)
  | None ->
      format_to_string (fun fmt ->
        F.fprintf fmt "expected type `%a', got  `%a' for Expression `%a'"
          pp_ty ty1 pp_ty ty2 pp_exp e1)

let catch_TypeError f =
  try f()
  with Constructors.TypeError(ty1,ty2,e1,me2,s) ->
    print_string (typeError_to_string (ty1,ty2,e1,me2,s));
    raise (Constructors.TypeError(ty1,ty2,e1,me2,s))
