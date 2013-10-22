(** Types for parsing: Types and expressions *)

module T = Type
module E = Expr
module Ht = Hashtbl
module G = Game

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

type proofstate =
  { ps_tvars   : (string, T.Lenvar.id) Ht.t; 
    ps_gvars   : (string, T.Groupvar.id) Ht.t; 
    ps_rodecls : (string, Hsym.t) Ht.t;
    ps_odecls  : (string, Osym.t) Ht.t;
    ps_adecls  : (string, Asym.t) Ht.t;
    ps_emdecls : (string, Esym.t) Ht.t;
    ps_assm    : (string, Assumption.assumption_decision) Ht.t;
    ps_vars    : (string, Vsym.t) Ht.t;
    ps_goals   : (G.judgment list) option
  }

let mk_ps () =
  { ps_tvars   = Ht.create 20;
    ps_gvars   = Ht.create 20;
    ps_rodecls = Ht.create 20;
    ps_odecls  = Ht.create 20; 
    ps_adecls  = Ht.create 20;
    ps_emdecls = Ht.create 20;
    ps_assm    = Ht.create 5;
    ps_vars    = Ht.create 20; 
    ps_goals   = None }

let ps_resetvars ps =
  { ps with
    ps_vars    = Ht.create 20;
    ps_goals   = None }

let create_lenvar ps s =
  try Ht.find ps.ps_tvars s 
  with Not_found ->
    let lv = T.Lenvar.mk s in
    Ht.add ps.ps_tvars s lv;
    lv

let create_groupvar ps s =
  try Ht.find ps.ps_gvars s 
  with Not_found ->
    let gv = T.Groupvar.mk s in
    Ht.add ps.ps_gvars s gv;
    gv

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

let create_var reuse ps s ty =
  if Ht.mem ps.ps_vars s then (
    if reuse then Ht.find ps.ps_vars s
    else failwith (Format.sprintf "Variable %s reused" s)
  ) else (
    let v = Vsym.mk s ty in
    Ht.add ps.ps_vars s v;
    v
  )

let bind_of_parse_bind ps lH = 
  List.map (fun (x,h) -> 
    let h = 
      try Ht.find ps.ps_rodecls h with Not_found ->
        failwith (Format.sprintf "undefined random oracle %s" h) in
    let tdom = h.Hsym.dom in
    let x = create_var true ps x tdom in
    x,h) lH
    
let expr_of_parse_expr ps pe0 =
  let rec go pe = 
    match pe with
    | V(s)         -> 
      let v = 
        try Ht.find ps.ps_vars s with Not_found ->
          failwith (Format.sprintf "undefined variable %s" s) in
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
      failwith (Format.sprintf "undefined hash symbol %s" s)
    | SApp(s,[a;b]) when Ht.mem ps.ps_emdecls s -> 
      let es = Ht.find ps.ps_emdecls s in
      E.mk_EMap es (go a) (go b)
    | SApp(s,_) when Ht.mem ps.ps_emdecls s ->
      failwith (Format.sprintf "bilinear map %s expects two arguments" s)
    | SApp(s,_) ->
      failwith (Format.sprintf "undefined function symbol %s" s)
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
      (match e1.E.e_ty.T.ty_node with
      | T.Fq -> E.mk_FMult [e1;e2]
      | T.G _ -> E.mk_GMult [e1;e2]
      | _    -> failwith "type error")
  in go pe0

let lcmd_of_parse_lcmd reuse ps lcmd =
  match lcmd with
  | LLet(s,e) ->
      let e = expr_of_parse_expr ps e in
      let v = create_var reuse ps s e.Expr.e_ty in
      Game.LLet(v,e)
  | LSamp(s,t,es) ->
      let t = ty_of_parse_ty ps t in
      let es = List.map (expr_of_parse_expr ps) es in
      let v = create_var reuse ps s t in
      Game.LSamp(v,(t,es))
  | LGuard(e) ->
      Game.LGuard(expr_of_parse_expr ps e)
  | LBind(_) -> assert false (* not implemented yet *)

let odef_of_parse_odef reuse ps (oname, vs, (m,e)) =
  let osym = 
    try Ht.find ps.ps_odecls oname
    with Not_found -> failwith "oracle name not declared" in
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
      Game.GLet(v,e)
  | GSamp(s,t,es) ->
      let t = ty_of_parse_ty ps t in
      let es = List.map (expr_of_parse_expr ps) es in
      let v = create_var reuse ps s t in
      Game.GSamp(v,(t,es))
  | GCall(vs,aname,e,os) ->
      let asym = try Ht.find ps.ps_adecls aname
                 with Not_found -> failwith "adversary name not declared"
      in
      let e = expr_of_parse_expr ps e in
      if not (Type.ty_equal e.Expr.e_ty asym.Asym.dom) then
        failwith "adversary argument has wrong type";
      let os = List.map (odef_of_parse_odef reuse ps) os in
      (match asym.Asym.codom.Type.ty_node, vs with
       | Type.Prod([]), [] -> Game.GCall([], asym, e, os)
       | Type.Prod(ts), vs when List.length ts = List.length vs ->
           let vts = List.combine vs ts in
           let vs = List.map (fun (v,t) -> create_var reuse ps v t) vts in
           Game.GCall(vs, asym, e, os)
       | _, [v] ->
           let v = create_var reuse ps v asym.Asym.codom in
           Game.GCall([v], asym, e, os)           
       | _ -> assert false)

let gdef_of_parse_gdef reuse ps gd =
  List.map (fun gc -> gcmd_of_parse_gcmd reuse ps gc) gd

let ju_of_parse_ju reuse ps gd e =
  let gd = gdef_of_parse_gdef reuse ps gd in
  let ju = { Game.ju_gdef = gd; 
             Game.ju_ev = expr_of_parse_expr ps e } in
  Wf.wf_ju ju;
  ju

(* ----------------------------------------------------------------------- *)
(** {3 Types for parsed proof scripts and tactics} *)

type tactic =
    Rnorm
  | Rnorm_nounfold    
  | Rnorm_unknown of string list
  | Rswap of int * int
  | Rctxt_ev of string * parse_expr
  | Rrandom of int * (string * parse_expr) option * string * parse_expr * string
  | Rrandom_oracle of (int * int * int) * (string * parse_expr) option * string * parse_expr * string
  | Requiv of gdef * parse_expr option
  | Rbddh of string
  | Rddh of string
  | Rassm of [`LtoR | `RtoL] * string * string list
  | Rlet_abstract of int * string * parse_expr
  | Rlet_unfold of int
  | Rindep
  | Rbad of int * string
  | Rexcept of int * parse_expr list
  | Rexcept_oracle of (int * int * int) * parse_expr list

type instr =
  | RODecl     of string * parse_ty * parse_ty
  | EMDecl     of string * string * string * string
  | ODecl      of string * parse_ty * parse_ty
  | ADecl      of string * parse_ty * parse_ty
  | AssmDec    of string * gdef * gdef * string list
  | Judgment   of gdef * parse_expr
  | PrintGoals of string
  | Apply      of tactic

type theory = instr list
