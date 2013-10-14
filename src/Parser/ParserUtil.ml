(** Types for parsing: Types and expressions *)

module T = Type
module E = Expr
module Ht = Hashtbl

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

let expr_of_parse_expr ?ht:(ht=Ht.create 20) pe0 =
  let rec go pe = 
    match pe with
    | V(s)         -> E.mk_V (Ht.find ht s)
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