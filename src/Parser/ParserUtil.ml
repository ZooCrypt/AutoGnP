(*s Types and conversion functions for parsed types, expressions, games, proof scripts, and tactics. *)

(*i*)
open TheoryTypes
open TheoryState
open Syms
open Gsyms
open ParserTypes

module E = Expr
module Ht = Hashtbl
module G = Game
module F = Format
module T = Type
module S = String

(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Utility functions} *)


(** Parser error with explanation. *)
exception ParseError of string

let fail_parse s = raise (ParseError s)

let create_var vmap s ty =
  if Ht.mem vmap s then
    failwith "create_var: variable already defined"
  else
    let v = Vsym.mk s ty in
    Ht.add vmap s v;
    v

(*i ----------------------------------------------------------------------- i*)
(* \hd{Conversion functions for parser-types} *)

let rec ty_of_parse_ty ts pty =
  match pty with
  | BS(s)     -> T.mk_BS(create_lenvar ts s)
  | Bool      -> T.mk_Bool
  | G(s)      -> T.mk_G(create_groupvar ts s)
  | Fq        -> T.mk_Fq
  | Prod(pts) -> T.mk_Prod (List.map (ty_of_parse_ty ts) pts)
      
let mk_Tuple es = 
  match es with
  | [e] -> e
  | _ -> E.mk_Tuple es

let bind_of_parse_bind vmap ts lH =
  List.map
    (fun (s,h) -> 
       let h = 
         try Ht.find ts.ts_rodecls h
         with Not_found ->
           fail_parse (F.sprintf "undefined random oracle %s" h)
       in
       let x = create_var vmap s h.Hsym.dom in
       (x, h))
    lH

let expr_of_parse_expr vmap ts pe0 =
  let rec go pe = 
    match pe with
    | V(s) ->
      let v =
        try Ht.find vmap s
        with Not_found ->
          fail_parse (F.sprintf "undefined variable %s (not in %s)"
                        s
                        (S.concat ","
                           (Ht.fold (fun v _ acc -> v::acc) vmap [])))
      in
      E.mk_V v
    | Tuple(es) -> E.mk_Tuple (List.map go es)
    | Proj(i,e) -> E.mk_Proj i (go e)
    | Exists(e1,e2,lH) -> 
      let lH = bind_of_parse_bind vmap ts lH in
      let e1 = go e1 in
      let e2 = go e2 in
      E.mk_Exists e1 e2 lH
    | HApp(s,es) when Ht.mem ts.ts_rodecls s -> 
      let h = Ht.find ts.ts_rodecls s in
      let es = mk_Tuple (List.map go es) in
      E.mk_H h es
    | HApp(s,_) ->
      fail_parse (F.sprintf "undefined hash symbol %s" s)
    | SApp(s,[a;b]) when Ht.mem ts.ts_emdecls s -> 
      let es = Ht.find ts.ts_emdecls s in
      E.mk_EMap es (go a) (go b)
    | SApp(s,_) when Ht.mem ts.ts_emdecls s ->
      fail_parse (F.sprintf "bilinear map %s expects two arguments" s)
    | SApp(s,_) ->
      fail_parse (F.sprintf "undefined function symbol %s" s)
    | CFNat(i)     -> E.mk_FNat i
    | CGen(s)      -> E.mk_GGen (create_groupvar ts s)
    | CZ(s)        -> E.mk_Z (create_lenvar ts s)
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
    | Log(e)       -> E.mk_GLog (go e)
    | Exp(e1,e2)   -> E.mk_GExp (go e1) (go e2)
    | Mult(e1,e2)  ->
      let e1 = go e1 in
      let e2 = go e2 in
      begin match e1.E.e_ty.T.ty_node with
      | T.Fq  -> E.mk_FMult [e1;e2]
      | T.G _ -> E.mk_GMult [e1;e2]
      | _     -> fail_parse "type error"
      end
  in go pe0

let lcmd_of_parse_lcmd vmap ts lcmd =
  match lcmd with
  | LLet(s,e) ->
    let e = expr_of_parse_expr vmap ts e in
    let v = create_var vmap s e.E.e_ty in
    G.LLet(v,e)
  | LSamp(s,t,es) ->
    let t = ty_of_parse_ty ts t in
    let es = List.map (expr_of_parse_expr vmap ts) es in
    let v = create_var vmap s t in
    G.LSamp(v,(t,es))
  | LGuard(e) ->
    G.LGuard(expr_of_parse_expr vmap ts e)
  | LBind(_) ->
    assert false (* not implemented yet *)

let odef_of_parse_odef vmap ts (oname, vs, (m,e)) =
  (*c variables declared in oracle are local *)
  let vmap = Ht.copy vmap in
  let osym = 
    try Ht.find ts.ts_odecls oname
    with Not_found -> fail_parse "oracle name not declared"
  in
  let vs = 
    match osym.Osym.dom.Type.ty_node, vs with
    | Type.Prod([]), [] -> []
    | Type.Prod(tys), vs when List.length tys = List.length vs ->
      let vts = List.combine vs tys in
      let vs = List.map (fun (v,t) -> create_var vmap v t) vts in
      vs
    | _, [v] -> [create_var vmap v osym.Osym.dom]
    | _ ->
      Util.tacerror "Pattern matching in oracle definition invalid: %a" Osym.pp osym
  in
  let m = List.map (lcmd_of_parse_lcmd vmap ts) m in
  let e = expr_of_parse_expr vmap ts e in
  (osym, vs, m, e)

let gcmd_of_parse_gcmd vmap ts gc =
  match gc with
  | GLet(s,e) ->
    let e = expr_of_parse_expr vmap ts e in
    let v = create_var vmap s e.E.e_ty in
    G.GLet(v,e)
  | GSamp(s,t,es) ->
    let t = ty_of_parse_ty ts t in
    let es = List.map (expr_of_parse_expr vmap ts) es in
    let v = create_var vmap s t in
    G.GSamp(v,(t,es))
  | GCall(vs,aname,e,os) ->
    let asym =
      try Ht.find ts.ts_adecls aname
      with Not_found -> fail_parse "adversary name not declared"
    in
    let e = expr_of_parse_expr vmap ts e in
    if not (Type.ty_equal e.E.e_ty asym.Asym.dom) then
      fail_parse "adversary argument has wrong type";
    let os = List.map (odef_of_parse_odef vmap ts) os in
    begin match asym.Asym.codom.Type.ty_node, vs with
    | Type.Prod([]), [] -> G.GCall([], asym, e, os)
    | Type.Prod(tys), vs when List.length tys = List.length vs ->
      let vts = List.combine vs tys in
      let vs = List.map (fun (v,t) -> create_var vmap v t) vts in
      G.GCall(vs, asym, e, os)
    | _, [v] ->
      let v = create_var vmap v asym.Asym.codom in
      G.GCall([v], asym, e, os)           
    | _ -> assert false
    end

let gdef_of_parse_gdef vmap ts gd =
  List.map (fun gc -> gcmd_of_parse_gcmd vmap ts gc) gd

let ju_of_parse_ju vmap ts gd e =
  let gd = gdef_of_parse_gdef vmap ts gd in
  let ju =
    { G.ju_gdef = gd; 
      G.ju_ev = expr_of_parse_expr vmap ts e }
  in
  Wf.wf_ju Wf.NoCheckDivZero ju;
  ju
