(** Types for parsing: Types and expressions *)

module T = Type
module E = Expr
module Ht = Hashtbl
module G = Game


type parse_ty =
  | BS of string
  | Bool
  | G
  | GT
  | Fq
  | Prod of parse_ty list

type parse_expr =
  | V     of string
  | SApp  of string * parse_expr list
  | Tuple of parse_expr list
  | Proj  of int * parse_expr
  | Cnst  of Expr.cnst
  | Mult  of parse_expr * parse_expr
  | Plus  of parse_expr * parse_expr
  | Exp   of parse_expr * parse_expr
  | EMap  of parse_expr * parse_expr
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
  | ElemH of parse_expr * string

let rec ty_of_parse_ty ?ht:(ht=Ht.create 20) pty =
  match pty with
  | BS(s) ->
      let lv =
        try Ht.find ht s
        with
        Not_found ->
          let lv = T.Lenvar.mk s in
          Ht.add ht s lv;
          lv
      in T.mk_BS(lv)
  | Bool -> T.mk_Bool
  | G -> T.mk_G
  | GT -> T.mk_GT
  | Fq -> T.mk_Fq
  | Prod(pts) ->
      T.mk_Prod (List.map (ty_of_parse_ty ~ht) pts)

let expr_of_parse_expr ht pe0 =
  let rec go pe = 
    match pe with
    | V(s)         -> E.mk_V (try Ht.find ht s
                              with Not_found ->
                                     failwith (Format.sprintf "undefined variable %s" s))
    | Tuple(es)    -> E.mk_Tuple (List.map go es)
    | Proj(i,e)    -> E.mk_Proj i (go e)
    | ElemH(_e,_s) -> failwith "not implemented"
    | SApp(_s,_es) -> failwith "not implemented"
    | Cnst(E.FOne) -> E.mk_FOne
    | Cnst(E.FZ)   -> E.mk_FZ
    | Cnst(E.GGen) -> E.mk_GGen  
    | Cnst(E.Z)    -> failwith "not implemented"
    | Cnst(E.B b)  -> E.mk_B b
    | EMap(e1,e2)  -> E.mk_EMap (go e1) (go e2)
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
        (match e.E.e_ty.T.ty_node with
         | T.G  -> E.mk_GLog e
         | T.GT -> E.mk_GTLog e
         | _    -> failwith "type error")
    | Exp(e1,e2)  ->
        let e1 = go e1 in
        let e2 = go e2 in
        (match e1.E.e_ty.T.ty_node with
         | T.G  -> E.mk_GExp e1 e2
         | T.GT -> E.mk_GTExp e1 e2
         | _    -> failwith "type error")
    | Mult(e1,e2)  ->
        let e1 = go e1 in
        let e2 = go e2 in
        (match e1.E.e_ty.T.ty_node with
         | T.Fq -> E.mk_FMult [e1;e2]
         | T.G  -> E.mk_GMult e1 e2
         | T.GT -> E.mk_GTMult e1 e2
         | _    -> failwith "type error")
  in go pe0

type lcmd =
    LLet   of string * parse_expr
      (* let x = e *)
  | LBind  of string list * string
      (* (x1,..,xk) <- L_h *)
  | LSamp  of string * parse_ty * parse_expr list
      (* x <-$ t \ e1,..,ek *)
  | LGuard of parse_expr
      (* e *)

type lcomp = lcmd list * parse_expr

type odef =
  string * string list * lcomp
  (* o(x) = [ e | m ], get types from osym decl *)

type gcmd =
    GLet  of string * parse_expr
  | GSamp of string * parse_ty * parse_expr list
  | GCall of string list * string * parse_expr * odef list

(* game definition *)
type gdef = gcmd list

type tactic =
    Rnorm
  | Rrandom of int * string * parse_expr * string * parse_expr
  | Rrandom_oracle of int * int * int * string * parse_expr * string * parse_expr

type instr =
    ODecl of string * parse_ty * parse_ty
  | ADecl of string * parse_ty * parse_ty
  | Judgment of gdef * parse_expr
  | PrintGoals of string
  | Apply of tactic

type theory = instr list

type proofstate =
  { ps_odecls : (string,Osym.t) Ht.t;
    ps_adecls : (string,Asym.t) Ht.t;
    ps_vars   : (string,Vsym.t) Ht.t;
    ps_goals  : (G.judgment list) option
  }

let mk_ps = { ps_odecls = Ht.create 20; ps_adecls = Ht.create 20;
              ps_vars = Ht.create 20; ps_goals = None }

let create_var ps s ty =
  if Ht.mem ps.ps_vars s then failwith "Variable name reused";
  let v = Vsym.mk s ty in
  Ht.add ps.ps_vars s v;
  v

let lcmd_of_parse_lcmd ps lcmd =
  match lcmd with
  | LLet(s,e) ->
      let e = expr_of_parse_expr ps.ps_vars e in
      let v = create_var ps s e.Expr.e_ty in
      Game.LLet(v,e)
  | LSamp(s,t,es) ->
      let t = ty_of_parse_ty t in
      let es = List.map (expr_of_parse_expr ps.ps_vars) es in
      let v = create_var ps s t in
      Game.LSamp(v,(t,es))
  | LGuard(e) ->
      Game.LGuard(expr_of_parse_expr ps.ps_vars e)
  | LBind(_) -> assert false (* not implemented yet *)

let odef_of_parse_odef ps (oname, vs, (m,e)) =
  let osym = try Ht.find ps.ps_odecls oname
             with Not_found -> failwith "oracle name not declared"
  in
  let vs = 
    (match osym.Osym.dom.Type.ty_node, vs with
     | Type.Prod([]), [] -> []
     | Type.Prod(ts), vs when List.length ts = List.length vs ->
         let vts = List.combine vs ts in
         let vs = List.map (fun (v,t) -> create_var ps v t) vts in
         vs
     | _, [v] -> [create_var ps v osym.Osym.dom]
     | _ -> assert false)
  in
  let m = List.map (lcmd_of_parse_lcmd ps) m in
  let e = expr_of_parse_expr ps.ps_vars e in
  (osym, vs, m, e)

let gcmd_of_parse_gcmd ps gc =
  match gc with
  | GLet(s,e) ->
      let e = expr_of_parse_expr ps.ps_vars e in
      let v = create_var ps s e.Expr.e_ty in
      Game.GLet(v,e)
  | GSamp(s,t,es) ->
      let t = ty_of_parse_ty t in
      let es = List.map (expr_of_parse_expr ps.ps_vars) es in
      let v = create_var ps s t in
      Game.GSamp(v,(t,es))
  | GCall(vs,aname,e,os) ->
      let asym = try Ht.find ps.ps_adecls aname
                 with Not_found -> failwith "adversary name not declared"
      in
      let e = expr_of_parse_expr ps.ps_vars e in
      if not (Type.ty_equal e.Expr.e_ty asym.Asym.dom) then
        failwith "adversary argument has wrong type";
      let os = List.map (odef_of_parse_odef ps) os in
      (match asym.Asym.codom.Type.ty_node, vs with
       | Type.Prod([]), [] -> Game.GCall([], asym, e, os)
       | Type.Prod(ts), vs when List.length ts = List.length vs ->
           let vts = List.combine vs ts in
           let vs = List.map (fun (v,t) -> create_var ps v t) vts in
           Game.GCall(vs, asym, e, os)
       | _, [v] ->
           let v = create_var ps v asym.Asym.codom in
           Game.GCall([v], asym, e, os)           
       | _ -> assert false)

let gdef_of_parse_gdef ps gd =
  List.map (fun gc -> gcmd_of_parse_gcmd ps gc) gd

let ju_of_parse_ju ps gd e =
  let gd = gdef_of_parse_gdef ps gd in
  { Game.ju_gdef = gd; Game.ju_ev = expr_of_parse_expr ps.ps_vars e }
