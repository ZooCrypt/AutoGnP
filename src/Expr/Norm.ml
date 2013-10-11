open Type
open Expr
module S = Singular

let mk_gexp p = mk_GExp mk_GGen p

let mk_gtexp p = mk_GTExp mk_GTGen p

let destr_gexp g = 
  let (g1,p) = destr_GExp g in
  assert (e_equal g1 mk_GGen);
  p

let destr_gtexp g = 
  let (g1,p) = destr_GTExp g in
  assert (e_equal g1 mk_GTGen);
  p

let destr_xor e = 
  match e.e_node with Nary(Xor, l) -> l | _ -> [e]

let norm_ggt e =   
  match e.e_ty.ty_node with
  | G -> mk_gexp (mk_GLog e)   (* g ^ (log x) *)
  | GT -> mk_gtexp (mk_GTLog e) (* e(g,g) (tlog x) *)
  | Fq | Bool | BS _ -> e
  | Prod _ -> e

let mk_proj_simpl i e = 
  match e.e_node with 
  | Tuple es -> 
    (try List.nth es i with Invalid_argument _ -> assert false)
  | _ -> mk_Proj i e

let is_field_op = function
  | FOpp | FMinus | FInv | FDiv -> true
  | GMult | GExp | GLog 
  | EMap | GTMult | GTExp | GTLog 
  | Eq | Ifte | Not -> false 

let is_field_nop = function
  | FPlus | FMult -> true
  | Xor | Land    -> false

let rec mk_simpl_op op l =
  match op, l with
  | GExp, [g1;p1] ->
    (* g1 is necessary of the form g ^ a *)
    let a = destr_gexp g1 in
    let p = norm_field_expr (mk_FMult [a; p1]) in
    mk_gexp p
  | GLog, [g1] -> destr_gexp g1 
  | GTExp, [g1;p1] ->
    let a = destr_gtexp g1 in
    let p = norm_field_expr (mk_FMult[a; p1]) in
    mk_gtexp p
  | GTLog, [g1] -> destr_gtexp g1
  | EMap, [g1;g2] -> (* e(g^a,g^b) -> e(g,g)^ab *)
    let p1 = destr_gexp g1 in
    let p2 = destr_gexp g2 in
    let p = norm_field_expr (mk_FMult [p1; p2]) in
    mk_gtexp p
  | GMult, [e1;e2] ->
    let p1 = destr_gexp e1 in
    let p2 = destr_gexp e2 in
    let p = norm_field_expr (mk_FPlus [p1; p2]) in
    mk_gexp p 
  | GTMult, [e1;e2] ->
    let p1 = destr_gtexp e1 in
    let p2 = destr_gtexp e2 in
    let p = norm_field_expr (mk_FPlus [p1; p2]) in
    mk_gtexp p
 
  | Eq, [e1;e2] -> 
    if e_equal e1 e2 then mk_True else mk_Eq e1 e2
  | Ifte, [e1;e2;e3] ->
    if is_True e1 then e2 
    else if is_False e1 then e3 
    else if e_equal e2 e3 then e2
    else mk_Ifte e1 e2 e3
  | Not, [e] ->
    if is_True e then mk_False
    else if is_False e then mk_True
    else mk_Not e
  | (        GExp   | GLog  | GMult
    | EMap | GTExp  | GTLog | GTMult
    | FOpp | FMinus | FInv  | FDiv 
    | Eq   | Ifte   | Not)           , _ -> assert false

and mk_simpl_nop op l =
  (* TODO flattening, for xor and land *)
  match op with
  | FPlus  | FMult  ->
    assert false (* norm_expr_field should be called instead *)
  | Xor -> 
    let l = List.flatten (List.map destr_xor l) in
    let l = List.sort e_compare l in
    let rec aux l = 
      match l with
      | [] | [_] -> l
      | e1::((e2::l) as l1) -> 
        if e_equal e1 e2 then aux l else e1 :: aux l1 in
    mk_Xor (aux l)
      
  | Land -> 
    let l = List.flatten (List.map destr_xor l) in
    let l = List.sort e_compare l in
    let rec aux l = 
      match l with
      | [] -> []
      | [e] -> 
        if is_True e then [] 
        else if is_False e then raise Not_found
        else l
      | e1::((e2::_) as l1) -> 
        if is_False e1 then raise Not_found 
        else if e_equal e1 e2 || is_True e1 then aux l1
        else e1 :: aux l1 in
    try 
      let l = aux l in
      if l = [] then mk_True 
      else mk_Land l 
    with Not_found -> mk_False
    
and norm_expr e = 
  match e.e_node with
  | V _ -> norm_ggt e 
  | Cnst GGen ->  mk_gexp mk_FOne
  | Cnst _ -> e
  | H(h,e) -> norm_ggt (mk_H h (norm_expr e))
  | Tuple l -> mk_Tuple (List.map norm_expr l)
  | Proj(i,e) -> mk_proj_simpl i (norm_expr e)
  | ElemH(e,h) ->
    mk_ElemH (norm_expr e) h
  | App (op, l) ->
    if is_field_op op then norm_field_expr e
    else
      let l = List.map norm_expr l in
      mk_simpl_op op l
  | Nary(nop, l) ->
    if is_field_nop nop then norm_field_expr e
    else
      let l = List.map norm_expr l in
      mk_simpl_nop nop l 
 
and norm_field_expr e = 
  let before e = 
    match e.e_node with
    | Cnst FOne | Cnst FZ
    | App (FOpp,[_]) | App (FInv,[_])
    | App (FMinus,[_;_]) | App (FDiv,[_;_])
    | Nary (FPlus, _) | Nary (FMult, _)  -> e
    | App(GLog, [e]) -> destr_gexp (norm_expr e)
    | App(GTLog, [e]) -> destr_gtexp (norm_expr e)
    | _ -> norm_expr e in
  S.norm before e 

  






