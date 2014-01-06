(** Types for parsing: Types and expressions *)

open Util
open Proofstate

module E = Expr
module Ht = Hashtbl
module G = Game
module F = Format

(** Parser error with explanation *)
exception ParseError of string

let fail_parse s = raise (ParseError s)

let create_var reuse ps s ty =
  match Proofstate.create_var reuse ps s ty with
  | None -> fail_parse (F.sprintf "Variable %s already defined" s)
  | Some v -> v

(* ----------------------------------------------------------------------- *)
(** {1 Types for parsed types, expressions, and games } *)

type parse_ty =
  | BS of string
  | Bool
  | G of string
  | Fq
  | Prod of parse_ty list

type parse_expr =
  | V     of string
  | SApp  of string * parse_expr list
  | HApp  of string * parse_expr list
  | Tuple of parse_expr list
  | Proj  of int * parse_expr
  | CB    of bool
  | CZ    of string
  | CGen  of string
  | CFNat of int
  | Mult  of parse_expr * parse_expr
  | Plus  of parse_expr * parse_expr
  | Exp   of parse_expr * parse_expr
  | Log   of parse_expr
  | Opp   of parse_expr
  | Minus of parse_expr * parse_expr
  | Inv   of parse_expr
  | Div   of parse_expr * parse_expr
  | Eq    of parse_expr * parse_expr
  | Not   of parse_expr
  | Ifte  of parse_expr * parse_expr * parse_expr
  | Land  of parse_expr * parse_expr
  | Xor   of parse_expr * parse_expr
  | ElemH of parse_expr * parse_expr * (string * string) list

type lcmd =
    LLet   of string * parse_expr
  | LBind  of string list * string
  | LSamp  of string * parse_ty * parse_expr list
  | LGuard of parse_expr

type lcomp = lcmd list * parse_expr

type odef = string * string list * lcomp

type gcmd =
    GLet  of string * parse_expr
  | GSamp of string * parse_ty * parse_expr list
  | GCall of string list * string * parse_expr * odef list

type gdef = gcmd list

(* ----------------------------------------------------------------------- *)
(** {2 Conversion functions for parser-types } *)

let rec ty_of_parse_ty ps pty =
  match pty with
  | BS(s)     -> T.mk_BS(create_lenvar ps s)
  | Bool      -> T.mk_Bool
  | G(s)      -> T.mk_G(create_groupvar ps s)
  | Fq        -> T.mk_Fq
  | Prod(pts) -> T.mk_Prod (List.map (ty_of_parse_ty ps) pts)
      
let mk_Tuple es = 
  match es with
  | [e] -> e
  | _ -> E.mk_Tuple es

let bind_of_parse_bind ps lH = 
  List.map
    (fun (s,h) -> 
       let h = 
         try Ht.find ps.ps_rodecls h
         with Not_found ->
           fail_parse (F.sprintf "undefined random oracle %s" h)
       in
       let x = create_var_reuse ps s h.Hsym.dom in
       (x, h))
    lH

let expr_of_parse_expr ps pe0 =
  let rec go pe = 
    match pe with
    | V(s)         -> 
      let v = 
        try Ht.find ps.ps_vars s
        with Not_found ->
          fail_parse (F.sprintf "undefined variable %s" s)
      in
      E.mk_V v
    | Tuple(es)    -> E.mk_Tuple (List.map go es)
    | Proj(i,e)    -> E.mk_Proj i (go e)
    | ElemH(e1,e2,lH) -> 
      let e1 = go e1 in
      let lH = bind_of_parse_bind ps lH in
      let e2 = go e2 in
      E.mk_ElemH e1 e2 lH
    | HApp(s,es) when Ht.mem ps.ps_rodecls s -> 
      let h = Ht.find ps.ps_rodecls s in
      let es = mk_Tuple (List.map go es) in
      E.mk_H h es
    | HApp(s,_) ->
      fail_parse (F.sprintf "undefined hash symbol %s" s)
    | SApp(s,[a;b]) when Ht.mem ps.ps_emdecls s -> 
      let es = Ht.find ps.ps_emdecls s in
      E.mk_EMap es (go a) (go b)
    | SApp(s,_) when Ht.mem ps.ps_emdecls s ->
      fail_parse (F.sprintf "bilinear map %s expects two arguments" s)
    | SApp(s,_) ->
      fail_parse (F.sprintf "undefined function symbol %s" s)
    | CFNat(i)     -> E.mk_FNat i
    | CGen(s)      -> E.mk_GGen (create_groupvar ps s)
    | CZ(s)        -> E.mk_Z (create_lenvar ps s)
    | CB b         -> E.mk_B b
    | Plus(e1,e2)  -> E.mk_FPlus [go e1; go e2]
    | Minus(e1,e2) -> E.mk_FMinus (go e1) (go e2)
    | Div(e1,e2)   -> E.mk_FDiv (go e1) (go e2)
    | Land(e1,e2)  -> E.mk_Land [go e1; go e2]
    | Xor(e1,e2)   -> E.mk_Xor [go e1; go e2]
    | Eq(e1,e2)    -> E.mk_Eq (go e1) (go e2)
    | Ifte(e1,e2,e3) -> E.mk_Ifte (go e1) (go e2) (go e3)
    | Opp(e)       -> E.mk_FOpp (go e)
    | Inv(e)       -> E.mk_FInv (go e)
    | Not(e)       -> E.mk_Not (go e)    
    | Log(e)   -> 
      let e = go e in
      E.mk_GLog e
    | Exp(e1,e2)  ->
      let e1 = go e1 in
      let e2 = go e2 in
      E.mk_GExp e1 e2
    | Mult(e1,e2)  ->
      let e1 = go e1 in
      let e2 = go e2 in
      begin match e1.E.e_ty.T.ty_node with
      | T.Fq -> E.mk_FMult [e1;e2]
      | T.G _ -> E.mk_GMult [e1;e2]
      | _    -> fail_parse "type error"
      end
  in go pe0

let lcmd_of_parse_lcmd reuse ps lcmd =
  match lcmd with
  | LLet(s,e) ->
    let e = expr_of_parse_expr ps e in
    let v = create_var reuse ps s e.Expr.e_ty in
    G.LLet(v,e)
  | LSamp(s,t,es) ->
    let t = ty_of_parse_ty ps t in
    let es = List.map (expr_of_parse_expr ps) es in
    let v = create_var reuse ps s t in
    G.LSamp(v,(t,es))
  | LGuard(e) ->
    G.LGuard(expr_of_parse_expr ps e)
  | LBind(_) -> assert false (* not implemented yet *)

let odef_of_parse_odef reuse ps (oname, vs, (m,e)) =
  let osym = 
    try Ht.find ps.ps_odecls oname
    with Not_found -> fail_parse "oracle name not declared" in
  let vs = 
    match osym.Osym.dom.Type.ty_node, vs with
    | Type.Prod([]), [] -> []
    | Type.Prod(ts), vs when List.length ts = List.length vs ->
      let vts = List.combine vs ts in
      let vs = List.map (fun (v,t) -> create_var reuse ps v t) vts in
      vs
    | _, [v] -> [create_var reuse ps v osym.Osym.dom]
    | _ -> assert false in
  let m = List.map (lcmd_of_parse_lcmd reuse ps) m in
  let e = expr_of_parse_expr ps e in
  (osym, vs, m, e)

let gcmd_of_parse_gcmd reuse ps gc =
  match gc with
  | GLet(s,e) ->
    let e = expr_of_parse_expr ps e in
    let v = create_var reuse ps s e.Expr.e_ty in
    G.GLet(v,e)
  | GSamp(s,t,es) ->
    let t = ty_of_parse_ty ps t in
    let es = List.map (expr_of_parse_expr ps) es in
    let v = create_var reuse ps s t in
    G.GSamp(v,(t,es))
  | GCall(vs,aname,e,os) ->
    let asym = try Ht.find ps.ps_adecls aname
               with Not_found -> fail_parse "adversary name not declared"
    in
    let e = expr_of_parse_expr ps e in
    if not (Type.ty_equal e.Expr.e_ty asym.Asym.dom) then
      fail_parse "adversary argument has wrong type";
    let os = List.map (odef_of_parse_odef reuse ps) os in
    begin match asym.Asym.codom.Type.ty_node, vs with
    | Type.Prod([]), [] -> G.GCall([], asym, e, os)
    | Type.Prod(ts), vs when List.length ts = List.length vs ->
      let vts = List.combine vs ts in
      let vs = List.map (fun (v,t) -> create_var reuse ps v t) vts in
      G.GCall(vs, asym, e, os)
    | _, [v] ->
      let v = create_var reuse ps v asym.Asym.codom in
      G.GCall([v], asym, e, os)           
    | _ -> assert false
    end

let gdef_of_parse_gdef reuse ps gd =
  List.map (fun gc -> gcmd_of_parse_gcmd reuse ps gc) gd

let ju_of_parse_ju reuse ps gd e =
  let gd = gdef_of_parse_gdef reuse ps gd in
  let ju = { G.ju_gdef = gd; 
             G.ju_ev = expr_of_parse_expr ps e } in
  Wf.wf_ju Wf.NoCheckDivZero ju;
  ju

(* ----------------------------------------------------------------------- *)
(** {3 Types for parsed proof scripts and tactics} *)

type tactic =
    Rnorm
  | Rnorm_nounfold    
  | Rnorm_unknown of string list
  | Rswap of int * int
  | Rswap_oracle of G.ocmd_pos * int  
  | Rctxt_ev of string * parse_expr * int
  | Rrandom of int * (string * parse_expr) option * string * parse_expr * string
  | Rrandom_oracle of G.ocmd_pos * (string * parse_expr) option * string * parse_expr * string
  | Requiv of gdef * parse_expr option
  | Rassm of direction * string * string list
  | Rlet_abstract of int * string * parse_expr
  | Rlet_unfold of int
  | Rindep
  | Rbad of int * string
  | Rexcept of int * parse_expr list
  | Rexcept_oracle of G.ocmd_pos * parse_expr list
  | Radd_test of G.ocmd_pos * parse_expr * string * string list
  | Rrewrite_oracle of G.ocmd_pos * direction

type instr =
  | RODecl     of string * parse_ty * parse_ty
  | EMDecl     of string * string * string * string
  | ODecl      of string * parse_ty * parse_ty
  | ADecl      of string * parse_ty * parse_ty
  | AssmDec    of string * gdef * gdef * string list
  | Judgment   of gdef * parse_expr
  | PrintGoals of string
  | PrintGoal of string  
  | Apply      of tactic
  | Admit
  | Last

type theory = instr list
