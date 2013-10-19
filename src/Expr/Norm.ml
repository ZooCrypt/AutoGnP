open Type
open Expr

module S = Singular

let mk_gexp gv p = mk_GExp (mk_GGen gv) p

let destr_gexp gv g = 
  let (g1,p) = try destr_GExp g with _ -> 
    Format.printf "destr_gexp %a@." pp_exp g;
    assert false
  in
  assert (e_equal g1 (mk_GGen gv));
  p

let destr_xor e = 
  match e.e_node with Nary(Xor, l) -> l | _ -> [e]

let norm_ggt e =   
  match e.e_ty.ty_node with
  | G gv -> mk_gexp gv (mk_GLog e)   (* g ^ (log x) *)
  | Fq | Bool | BS _ -> e
  | Prod _ -> e

let mk_proj_simpl i e = 
  match e.e_node with 
  | Tuple es -> 
    (try List.nth es i with Invalid_argument _ -> assert false)
  | _ -> mk_Proj i e

let rec mk_simpl_op op l =
  match op, l with
  | GExp, [g1;p1] ->
    (* g1 is necessary of the form g ^ a *)
    let gv = destr_G g1.e_ty in
    let a = destr_gexp gv g1 in
    let p = norm_field_expr (mk_FMult [a; p1]) in
    mk_gexp gv p
  | GLog gv, [g1] -> destr_gexp gv g1 
  | EMap es, [g1;g2] -> (* e(g^a,g^b) -> e(g,g)^ab *)
    let p1 = destr_gexp es.Esym.source1 g1 in
    let p2 = destr_gexp es.Esym.source2 g2 in
    let p = norm_field_expr (mk_FMult [p1; p2]) in
    mk_gexp es.Esym.target p
  | Eq, [e1;e2] -> 
    if e_equal e1 e2 then mk_True else mk_Eq e1 e2
  | Ifte, [e1;e2;e3] ->
    if is_True e1 then e2 
    else if is_False e1 then e3 
    else if e_equal e2 e3 then e2
    else norm_ggt (mk_Ifte e1 e2 e3)
  | Not, [e] ->
    if is_True e then mk_False
    else if is_False e then mk_True
    else mk_Not e
  | (        GExp   | GLog _ | EMap _
    | FOpp | FMinus | FInv   | FDiv 
    | Eq   | Ifte   | Not)           , _ -> assert false

and mk_simpl_nop op l =
  (* TODO flattening, for xor and land *)
  match op with
  | FPlus  | FMult  ->
    assert false (* norm_expr_field should be called instead *)
  | GMult ->
    let gv = match l with e::_ -> destr_G e.e_ty | _ -> assert false in
    let l = List.map (destr_gexp gv) l in
    let p = norm_field_expr (mk_FPlus l) in
    mk_gexp gv p
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
  | Cnst GGen ->  mk_gexp (destr_G e.e_ty) mk_FOne
  | Cnst _ -> e
  | H(h,e) -> norm_ggt (mk_H h (norm_expr e))
  | Tuple l -> mk_Tuple (List.map norm_expr l)
  | Proj(i,e) -> mk_proj_simpl i (norm_expr e)
  | ElemH(e1,e2,h) ->
    mk_ElemH (norm_expr e1) (norm_expr e2) h
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
    | Cnst (FNat _)
    | App (FOpp,[_]) | App (FInv,[_])
    | App (FMinus,[_;_]) | App (FDiv,[_;_])
    | Nary (FPlus, _) | Nary (FMult, _)  -> e
    | App(GLog gv, [e]) -> 
      let e = norm_expr e in
      (try destr_gexp gv e with _ -> assert false)
    | _ -> norm_expr e in
  S.norm before e 

let rec abbrev_ggen e =
  let e = e_sub_map abbrev_ggen e in
  match e.e_node with
  | App(GExp,[a;b]) ->
    if is_GGen a then (
       if e_equal b mk_FOne then a
       else if is_GLog b then destr_GLog b
      else e)
    else e
  | _ -> e

(* use norm_expr to check equality modulo equational theory *)
let e_equalmod e e' = e_equal (norm_expr e) (norm_expr e')







