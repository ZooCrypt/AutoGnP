(*s Types and conversion functions for parsed types, expressions, games, proof scripts, and tactics. *)

(*i*)
open Abbrevs
open Util
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
    tacerror "create_var: variable %s already defined" s
  else
    let v = Vsym.mk s ty in
    Ht.add vmap s v;
    v

(*i ----------------------------------------------------------------------- i*)
(* \hd{Conversion functions for parser-types} *)

let ty_of_parse_ty ts pty =
  let rec go pty =
    match pty with
    | Bool      -> T.mk_Bool
    | Fq        -> T.mk_Fq
    | Prod(pts) -> T.mk_Prod (List.map go pts)
    | BS(s)     -> T.mk_BS(create_lenvar ts s)
    | G(s)      -> T.mk_G(create_groupvar ts s)
  in
  go pty

let mk_Tuple es =
  match es with
  | [e] -> e
  | _ -> E.mk_Tuple es

let bind_of_parse_bind vmap ts lH =
  List.map
    (fun (s,h) ->
       let h =
         try Mstring.find h ts.ts_rodecls
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
    | HApp(s,es) when Mstring.mem s ts.ts_rodecls ->
      let h = Mstring.find s ts.ts_rodecls in
      let es = mk_Tuple (List.map go es) in
      E.mk_H h es
    | HApp(s,_) ->
      fail_parse (F.sprintf "undefined hash symbol %s" s)
    | SApp(s,[a;b]) when Mstring.mem s ts.ts_emdecls ->
      let es = Mstring.find s ts.ts_emdecls in
      E.mk_EMap es (go a) (go b)
    | SApp(s,_) when Mstring.mem s ts.ts_emdecls ->
      fail_parse (F.sprintf "bilinear map %s expects two arguments" s)
    | SApp(s,_) ->
      fail_parse (F.sprintf "undefined function symbol %s" s)
    | CFNat(i)     -> E.mk_FNat i
    | CB b         -> E.mk_B b
    | Plus(e1,e2)  -> E.mk_FPlus [go e1; go e2]
    | Minus(e1,e2) -> E.mk_FMinus (go e1) (go e2)
    | Land(e1,e2)  -> E.mk_Land [go e1; go e2]
    | Xor(e1,e2)   -> E.mk_Xor [go e1; go e2]
    | Eq(e1,e2)    -> E.mk_Eq (go e1) (go e2)
    | Ifte(e1,e2,e3) -> E.mk_Ifte (go e1) (go e2) (go e3)
    | Opp(e)       -> E.mk_FOpp (go e)
    | Inv(e)       -> E.mk_FInv (go e)
    | Not(e)       -> E.mk_Not (go e)
    | Log(e)       -> E.mk_GLog (go e)
    | Exp(e1,e2)   -> E.mk_GExp (go e1) (go e2)
    | CGen(s)      -> E.mk_GGen (create_groupvar ts s)
    | CZ(s)        -> E.mk_Z (create_lenvar ts s)
    | Div(e1,e2)   ->
      let e1 = go e1 in
      let e2 = go e2 in
      begin match e1.E.e_ty.T.ty_node with
      | T.Fq  -> E.mk_FDiv e1 e2
      | T.G _ -> E.mk_GMult [e1; E.mk_GInv e2]
      | _     -> fail_parse "type error"
      end
    | Mult(e1,e2)  ->
      let e1 = go e1 in
      let e2 = go e2 in
      begin match e1.E.e_ty.T.ty_node with
      | T.Fq  -> E.mk_FMult [e1;e2]
      | T.G _ -> E.mk_GMult [e1;e2]
      | _     -> fail_parse "type error"
      end
  in
  go pe0

let lcmd_of_parse_lcmd vmap ts lcmd =
  match lcmd with
  | LLet(s,e) ->
    let e = expr_of_parse_expr vmap ts e in
    let v = create_var vmap s e.E.e_ty in
    G.LLet(v,e)
  | LSamp(s,t,es) ->
    let t = ty_of_parse_ty ts t in
    let es = L.map (expr_of_parse_expr vmap ts) es in
    let v = create_var vmap s t in
    G.LSamp(v,(t,es))
  | LGuard(e) ->
    let e = expr_of_parse_expr vmap ts e in
    G.LGuard e
  | LBind(_) ->
    assert false (* not implemented yet *)

let odef_of_parse_odef vmap ts (oname, vs, (m,e)) =
  (*c variables declared in oracle are local *)
  let vmap = Ht.copy vmap in
  let osym =
    try Mstring.find oname ts.ts_odecls
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
      tacerror "Pattern matching in oracle definition invalid: %a" Osym.pp osym
  in
  let m = L.map (lcmd_of_parse_lcmd vmap ts) m in
  let e = expr_of_parse_expr vmap ts e in
  (osym, vs, m, e, false)

let gcmd_of_parse_gcmd vmap ts gc =
  match gc with
  | GLet(s,e) ->
    let e = expr_of_parse_expr vmap ts e in
    let v = create_var vmap s e.E.e_ty in
    G.GLet(v,e)
  | GSamp(s,t,es) ->
    let t = ty_of_parse_ty ts t in
    let es = L.map (expr_of_parse_expr vmap ts) es in
    let v = create_var vmap s t in
    G.GSamp(v,(t,es))
  | GCall(vs,aname,e,os) ->
    let asym =
      try Mstring.find aname ts.ts_adecls
      with Not_found -> fail_parse "adversary name not declared"
    in
    let e = expr_of_parse_expr vmap ts e in
    if not (Type.ty_equal e.E.e_ty asym.Asym.dom) then
      fail_parse "adversary argument has wrong type";
    let os = L.map (odef_of_parse_odef vmap ts) os in
    begin match asym.Asym.codom.Type.ty_node, vs with
    | Type.Prod([]), [] ->
      G.GCall([], asym, e, os)
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
  L.map (fun gc -> gcmd_of_parse_gcmd vmap ts gc) gd

let se_of_parse_se vmap ts gd e =
  let gd = gdef_of_parse_gdef vmap ts gd in
  let e  = expr_of_parse_expr vmap ts e in
  let se = { G.se_gdef = gd; G.se_ev = e } in
  Wf.wf_se Wf.NoCheckDivZero se;
  se
