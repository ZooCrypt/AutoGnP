(*s Types and conversion functions for parsed types, expressions, games, proof scripts, and tactics. *)

(*i*)
open Abbrevs
open Util
open TheoryTypes
open TheoryState
open Syms
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

let create_var (vmap : G.vmap) ts (qual : string qual) s ty =
  if Ht.mem vmap (qual,s) then (
    tacerror "create_var: variable %s already defined" s
  ) else (
    let q = map_qual (fun s -> Mstring.find s ts.ts_odecls) qual in
    let v = Vsym.mk_qual s q ty in
    Ht.add vmap (qual,s) v;
    v
  )

let get_oname_from_opos (se : G.sec_exp) (opos : G.ocmd_pos) : string = 
  let (i,j,_,_) = opos in
  match G.get_se_ctxt se i with
  | G.GCall(_,_,_,os), _ ->
     let (_,od,_) = split_n j os in
     let (os,_,_) = od in
     Id.name os.Osym.id
  | _ -> tacerror "Error, no Oracle definition at line %i" (i+1)
                  
(*i ----------------------------------------------------------------------- i*)
(* \hd{Conversion functions for parser-types} *)

let ty_of_parse_ty ts pty =
  let rec go pty =
    match pty with
    | Bool      -> T.mk_Bool
    | Fq        -> T.mk_Fq
    | Prod(pts) -> T.mk_Prod (L.map go pts)
    | BS(s)     -> T.mk_BS(create_lenvar ts s)
    | KeyPair s ->
       (try
         let f = Mstring.find (s ^ "_inv") ts.ts_permdecls in
           T.mk_KeyPair f.Psym.pid
         with Not_found -> tacerror "Undefined permutation %s" s)
    | PKey s ->
       (try
         let f = Mstring.find (s ^ "_inv") ts.ts_permdecls in
           T.mk_KeyElem T.PKey f.Psym.pid
         with Not_found -> tacerror "Undefined permutation %s" s)
    | SKey s ->
       (try
         let f = Mstring.find (s ^ "_inv") ts.ts_permdecls in
           T.mk_KeyElem T.SKey f.Psym.pid
         with Not_found -> tacerror "Undefined permutation %s" s)         
    | G(s)      -> T.mk_G(create_groupvar ts s)
  in
  go pty

let mk_Tuple es =
  match es with
  | [e] -> e
  | _ -> E.mk_Tuple es

let bind_of_parse_bind (vmap : G.vmap) ts lH =
  L.map
    (fun (s,h) ->
       let h =
         try Mstring.find h ts.ts_rodecls
         with Not_found ->
           fail_parse (F.sprintf "undefined random oracle %s" h)
       in
       let x = create_var vmap ts Unqual s h.Hsym.dom in
       (x, h))
    lH

let string_of_qvar (qual,s) =
  match qual with
  | Unqual -> s
  | Qual q -> q^"`"^s
let init_odef_params vmap_g ts ?(qual=true) oname vs = 
  let osym =
    try Oracle.mk_O(Mstring.find oname ts.ts_odecls)
    with Not_found -> try Oracle.mk_RO(Mstring.find oname ts.ts_rodecls)
                                      with Not_found -> fail_parse "oracle name not declared"
  in
  let qual = if qual then (Qual oname) else Unqual in
  let vs =
    match (Oracle.get_dom osym).Type.ty_node, vs with
    | Type.Prod([]), [] -> []
    | Type.Prod(tys), vs when L.length tys = L.length vs ->
      L.map
        (fun (v,t) -> create_var vmap_g ts qual v t)
        (L.combine vs tys)
    | _, [v] ->
      [create_var vmap_g ts qual v (Oracle.get_dom osym)]
    | _ ->
      tacerror "Pattern matching in oracle definition invalid: %a" Oracle.pp osym
  in
  vs,osym

let rec expr_of_parse_expr (vmap : G.vmap) ts (qual : string qual) pe0 =
  let rec go pe =
    match pe with
    | V(vqual,s) ->
      let v =
        try
          (try
             (* if not qualified, then search in current context *)
             (if vqual=Unqual then Ht.find vmap (qual,s) else raise Not_found)
           with Not_found ->
             (* search with the given qualifier next *)
             Ht.find vmap (vqual,s))
        with Not_found ->
          fail_parse (F.sprintf "undefined variable %s (not in %s)"
                        (string_of_qvar (qual,s))
                        (S.concat ","
                           (Ht.fold (fun qv _ acc -> (string_of_qvar qv)::acc) vmap [])))
      in
      E.mk_V v
    | Tuple(es) -> E.mk_Tuple (L.map go es)
    | ProjPermKey(ke,kp) -> E.mk_ProjPermKey ke (go kp)
    | Proj(i,e) -> E.mk_Proj i (go e)

    | SLookUp(s,es) ->
       let h = try Mstring.find s ts.ts_lkupdecls with
                 Not_found -> fail_parse (F.sprintf "Undefined random oracle %s" s) in
       let es = mk_Tuple (L.map go es) in
       E.mk_H h es
    | SApp(s,es) when Mstring.mem (s ^ "_inv") ts.ts_permdecls ->
       begin
         let f = Mstring.find (s ^ "_inv") ts.ts_permdecls in
         match es with
         | [k;e] -> E.mk_Perm f E.NotInv (go k) (go e)
         | k::es -> E.mk_Perm f E.NotInv (go k) (E.mk_Tuple (L.map go es))
         | _ -> fail_parse (F.sprintf "Permutation %s expects 2 arguments" s)
       end
    | SApp(s_inv,es) when Mstring.mem s_inv ts.ts_permdecls ->
       begin
         let f = Mstring.find s_inv ts.ts_permdecls in
         match es with
         | [k;e] -> E.mk_Perm f E.IsInv (go k) (go e)
         | k::es -> E.mk_Perm f E.IsInv (go k) (E.mk_Tuple (L.map go es))
         | _ -> fail_parse (F.sprintf "Permutation %s expects 2 arguments" s_inv)
       end
         
    | SApp(s,es) when Mstring.mem s ts.ts_rodecls ->
      let h = Mstring.find s ts.ts_rodecls in
      let es = mk_Tuple (L.map go es) in
      E.mk_H h es
             
    | SApp(s,[a;b]) when Mstring.mem s ts.ts_emdecls ->
      let es = Mstring.find s ts.ts_emdecls in
      E.mk_EMap es (go a) (go b)
    | SApp(s,_) when Mstring.mem s ts.ts_emdecls ->
      fail_parse (F.sprintf "bilinear map %s expects two arguments" s)
    | SApp(s,_) ->
      fail_parse (F.sprintf "undefined function symbol %s" s)
    | CFNat(i)		-> E.mk_FNat i
    | CB b		-> E.mk_B b
    | Plus(e1,e2)	-> E.mk_FPlus [go e1; go e2]
    | Minus(e1,e2)	-> E.mk_FMinus (go e1) (go e2)
    | Land(e1,e2)	-> E.mk_Land [go e1; go e2]
    | Xor(e1,e2)	-> E.mk_Xor [go e1; go e2]
    | Eq(e1,e2)         -> E.mk_Eq (go e1) (go e2)
    | Ifte(e1,e2,e3)	-> E.mk_Ifte (go e1) (go e2) (go e3)
    | Opp(e)		-> E.mk_FOpp (go e)
    | Inv(e)		-> E.mk_FInv (go e)
    | Not(e)		-> E.mk_Not (go e)
    | Log(e)		-> E.mk_GLog (go e)
    | Exp(e1,e2)	-> E.mk_GExp (go e1) (go e2)
    | CGen(s)		-> E.mk_GGen (create_groupvar ts s)
    | CZ(s)		-> E.mk_Z (create_lenvar ts s)
    | Quant(q,bd,pe)   ->
      let b = 
        List.map (fun (vs,oname) -> init_odef_params vmap ts ~qual:false oname vs) bd
      in
      let e = expr_of_parse_expr vmap ts qual pe in
      List.fold_left (fun acc x -> Expr.mk_Quant q x acc) e b

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

let lcmd_of_parse_lcmd (vmap : G.vmap) ts ~oname lcmd =
  let qual = Qual oname in
  match lcmd with
  | LLet(s,e) ->
    let e = expr_of_parse_expr vmap ts qual e in
    let v = create_var vmap ts qual s e.E.e_ty in
    G.LLet(v,e)
  | LSamp(s,t,es) ->
    let t = ty_of_parse_ty ts t in
    let es = L.map (expr_of_parse_expr vmap ts qual) es in
    let v = create_var vmap ts qual s t in
    G.LSamp(v,(t,es))
  | LGuard(e) ->
    G.LGuard (expr_of_parse_expr vmap ts qual e)
  | LBind(_) ->
    assert false (* not implemented yet *)

let obody_of_parse_obody vmap ts ~oname (m,e) =
  let m = L.map (lcmd_of_parse_lcmd vmap ts ~oname) m in
  let e = expr_of_parse_expr vmap ts (Qual oname) e in
  (m,e)

let odec_of_parse_odec vmap_g ts ~oname od =
  (*c create local vmap and use everywhere exceptin eq-hybrid-oracle *)
  let vmap_l = Ht.copy vmap_g in
  match od with
  | Odef ob ->
    G.Odef (obody_of_parse_obody vmap_l ts ~oname ob)
  | Ohybrid (ob1,ob2,ob3) ->
    G.Ohybrid
      { G.odef_less    = obody_of_parse_obody vmap_l ts ~oname ob1;
        G.odef_eq      = obody_of_parse_obody vmap_g ts ~oname ob2;
        G.odef_greater = obody_of_parse_obody vmap_l ts ~oname ob3; }
  
let odef_of_parse_odef vmap_g ts (oname, vs, odec) =
  let vs,osym = match init_odef_params vmap_g ts oname vs with
    | vs,(Oracle.O osym) -> vs,osym
    | _ -> tacerror "This should not be happening..." in
  let od = odec_of_parse_odec vmap_g ts ~oname odec in
  (osym, vs, od)

let gcmd_of_parse_gcmd (vmap : G.vmap) ts gc =
  match gc with
  | GLet(s,e) ->
    let e = expr_of_parse_expr vmap ts Unqual e in
    let v = create_var vmap ts Unqual s e.E.e_ty in
    G.GLet(v,e)
  | GAssert(e) ->
    let e = expr_of_parse_expr vmap ts Unqual e in
    G.GAssert(e)
  | GSamp(s,t,es) ->
    let t = ty_of_parse_ty ts t in
    let es = L.map (expr_of_parse_expr vmap ts Unqual) es in
    let v = create_var vmap ts Unqual s t in
    G.GSamp(v,(t,es))
  | GCall(vs,aname,e,os) ->
    let asym =
      try Mstring.find aname ts.ts_adecls
      with Not_found -> fail_parse "adversary name not declared"
    in
    let e = expr_of_parse_expr vmap ts Unqual e in
    if not (Type.ty_equal e.E.e_ty asym.Asym.dom) then
      fail_parse "adversary argument has wrong type";
    let os = L.map (odef_of_parse_odef vmap ts) os in
    let cty = asym.Asym.codom in
    begin match cty.Type.ty_node, vs with      
    | Type.Prod([]), [] ->
      G.GCall([], asym, e, os)
    | _, [v] ->
      let v = create_var vmap ts Unqual v asym.Asym.codom in
      G.GCall([v], asym, e, os)
    | Type.Prod(tys), vs ->
      if L.length tys <> L.length vs then
        tacerror "Parser: wrong argument for adversary return value, expected %i variables for type %a"
          (L.length vs)Type.pp_ty cty;
      let vts = L.combine vs tys in
      let vs = L.map (fun (v,t) -> create_var vmap ts Unqual v t) vts in
      G.GCall(vs, asym, e, os)
    | (Type.BS _|Type.Bool|Type.G _|Type.Fq|Type.Int|Type.KeyElem _|Type.KeyPair _)
      , ([] | _ :: _ :: _) -> 
      tacerror "Parser: wrong argument for adversary return value, expected one variable for type Bool"
          Type.pp_ty cty (L.length vs);
    end

let gdef_of_parse_gdef (vmap : G.vmap) ts gd =
  L.map (fun gc -> gcmd_of_parse_gcmd vmap ts gc) gd

let ev_of_parse_ev vmap ts pe =
  G.Event.mk (expr_of_parse_expr vmap ts Unqual pe)
                     
let se_of_parse_se (vmap : G.vmap) ts gd ev =
  let gd = gdef_of_parse_gdef vmap ts gd in
  let ev  = ev_of_parse_ev vmap ts ev in
  let se = { G.se_gdef = gd; G.se_ev = ev } in
  Wf.wf_se Wf.NoCheckDivZero se;
  se
