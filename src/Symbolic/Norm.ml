(*s Normal form computation for expressions. *)

(*i*)
open Abbrevs
open Type
open Expr
open ExprUtils
open Syms
(*i*)

let mk_gexp gv p = mk_GExp (mk_GGen gv) p

let destr_gexp gv g = 
  let (g1,p) = try destr_GExp g with _ -> 
    F.printf "destr_gexp %a@." pp_exp g;
    assert false
  in
  assert (e_equal g1 (mk_GGen gv));
  p

let rec norm_ggt e =   
  match e.e_ty.ty_node with
  | G gv -> mk_gexp gv (mk_GLog e)   (*i g ^ (log x) i*)

  | Fq | Bool | Int | BS _ -> e

  | Prod lt -> mk_Tuple (List.mapi (fun i _ -> norm_ggt (mk_Proj i e)) lt)

let mk_proj_simpl i e = 
  match e.e_node with 
  | Tuple es -> 
    (try List.nth es i with Invalid_argument _ -> assert false)
  | _ -> mk_Proj i e

let rec mk_simpl_op _strong op l =
  match op, l with
  | GExp gv, [g1;p1] ->
    (*i g1 is necessary of the form g ^ a i*)
    let a = destr_gexp gv g1 in
    let p = norm_field_expr (mk_FMult [a; p1]) in
    mk_gexp gv p
  | GLog gv, [g1] -> destr_gexp gv g1 
  | EMap es, [g1;g2] -> (*i e(g^a,g^b) -> e(g,g)^ab i*)
    let p1 = destr_gexp es.Esym.source1 g1 in
    let p2 = destr_gexp es.Esym.source2 g2 in
    let p = norm_field_expr (mk_FMult [p1; p2]) in
    mk_gexp es.Esym.target p
  | Eq, [e1;e2] ->
    if e_equal e1 e2 then mk_True 
    else if is_False e1 then mk_Not e2
    else if is_False e2 then mk_Not e1
    else if is_True e1 then  e2
    else if is_True e2 then e1
    else mk_Eq e1 e2
  | Ifte, [e1;e2;e3] ->
    if is_True e1 then e2 
    else if is_False e1 then e3 
    else if e_equal e2 e3 then e2
    else norm_ggt (mk_Ifte e1 e2 e3)
  | Not, [e] ->
    if is_True e then mk_False
    else if is_False e then mk_True
    else
      begin match e.e_node with
      | App(Not,[e]) -> e
      | _            -> mk_Not e
      end
  | (        GExp _ | GLog _ | EMap _
    | FOpp | FMinus | FInv   | FDiv 
    | Eq   | Ifte   | Not)           , _ -> assert false

and mk_simpl_nop strong op l =
  (*i TODO flattening, for xor and land i*)
  match op with
  | FPlus  | FMult  ->
    assert false (*i norm_expr_field should be called instead i*)
  | GMult ->
    let gv = match l with e::_ -> destr_G e.e_ty | _ -> assert false in
    let l = List.map (destr_gexp gv) l in
    let p = norm_field_expr (mk_FPlus l) in
    mk_gexp gv p
  | Xor -> 
    let l = List.flatten (List.map destr_Xor_nofail l) in
    let l = List.sort e_compare l in
    let e = List.hd l in
    let rec aux l = 
      match l with
      | [] | [_] -> l
      | e1::((e2::l) as l1) -> 
        if e_equal e1 e2 then aux l else e1 :: aux l1 in
    L.iter (fun e -> F.printf "%a " pp_exp e) l;
    let l = aux l in
    let l = List.filter (fun e -> not (is_Zero e)) l in
    if l = [] then mk_Zero e.e_ty 
    else mk_Xor (aux l)
      
  | Land ->
    (* FIXME: is this really usefull?
       we should handle conjunctions manually. *)
    let l = List.flatten (List.map destr_Land_nofail l) in
    let l = if strong then List.sort e_compare l else l in
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
    
and norm_expr ?strong:(strong=false) e = 
  match e.e_node with
  | V _ -> norm_ggt e 
  | Cnst GGen ->  mk_gexp (destr_G e.e_ty) mk_FOne
  | Cnst _ -> e
  | H(h,e) -> norm_ggt (mk_H h (norm_expr ~strong e))
  | Tuple l -> mk_Tuple (List.map (norm_expr ~strong) l)
  | Proj(i,e) -> mk_proj_simpl i (norm_expr ~strong e)
  | Exists(e1,e2,h) ->
    mk_Exists (norm_expr ~strong e1) (norm_expr ~strong e2) h
  | App (op, l) ->
    if is_field_op op then norm_field_expr e
    else
      let l = List.map (norm_expr ~strong) l in
      mk_simpl_op strong op l
  | Nary(nop, l) ->
    if is_field_nop nop then norm_field_expr e
    else
      let l = List.map (norm_expr ~strong) l in
      mk_simpl_nop strong nop l 
 
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
  CAS.norm before e 

let rec abbrev_ggen e =
  let e = e_sub_map abbrev_ggen e in
  match e.e_node with
  | App(GExp _,[a;b]) ->
    if is_GGen a then (
       if e_equal b mk_FOne then a
       else if is_GLog b then destr_GLog b
      else e)
    else e
  | _ -> e

let norm_expr_weak e = norm_expr ~strong:false e

let norm_expr_strong e = norm_expr ~strong:true e

(*i use norm_expr to check equality modulo equational theory i*)
let e_equalmod e e' = e_equal (norm_expr_strong e) (norm_expr_strong e')

let rm_tuple_proj e es =
  match es with
  | e1::es ->
    begin 
      try 
        let i, e2 = destr_Proj e1 in
        if i <> 0 then raise Not_found;
        if List.length es + 1 <> List.length (destr_Prod e2.e_ty) then 
          raise Not_found;
        List.iteri (fun i e -> 
          let i',e' = destr_Proj e in
          if i + 1 <> i' || not (e_equal e2 e') then raise Not_found) es;
        e2
      with Not_found | Destr_failure _ -> e
    end
  | _ -> e 

let rec remove_tuple_proj e =
  let e = e_sub_map remove_tuple_proj e in
  match e.e_node with
  | Tuple es -> rm_tuple_proj e es
  | _ -> e

let norm_expr_abbrev_weak e = abbrev_ggen (norm_expr_weak e)

let norm_expr_abbrev_strong e = abbrev_ggen (norm_expr_strong e)

let norm_expr_nice e = remove_tuple_proj (abbrev_ggen (norm_expr_weak e))

let destr_Eq_norm e =
  match e.e_node with
  | App(Eq,[e1;e2]) ->
    begin match e1.e_ty.ty_node with
    | G(_gid) -> Some (norm_expr_strong (mk_FMinus (mk_GLog e1) (mk_GLog e2)))
    | Fq      -> Some (norm_expr_strong (mk_FMinus e1 e2))
    | _       -> None
    end
  | _ ->
    None

let destr_Neq_norm e =
  match e.e_node with
  | App(Not,[e1]) -> destr_Eq_norm e1
  | _             -> None
