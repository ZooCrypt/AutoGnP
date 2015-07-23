(*s Normal form computation for expressions. *)

(*i*)
open Abbrevs
open Type
open Expr
open ExprUtils
open Syms
open Util

let _log_i ls = mk_logger "Norm" Bolt.Level.INFO "Norm" ls

(*i*)

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

  | KeyPair _ | KeyElem _ -> e

  | Prod lt -> mk_Tuple (List.mapi (fun i _ -> norm_ggt (mk_Proj i e)) lt)

let mk_proj_simpl i e =
  match e.e_node with
  | Tuple es ->
    (try List.nth es i with Invalid_argument _ -> assert false)
  | _ -> mk_Proj i e

let common_diff xs1 xs2 =
  let rec rm acc y xs =
    match xs with
    | x::xs when x = y -> Some (L.rev_append acc xs)
    | x::xs            -> rm (x::acc) y xs
    | []               -> None
  in  
  let rec go common nc1 xs1 xs2 =
    match xs1 with
    | []  -> (common,nc1,xs2)
    | x1::xs1 ->
      begin match rm [] x1 xs2 with
      | Some xs2 -> go (x1::common) nc1 xs1 xs2
      | None     -> go common (x1::nc1) xs1 xs2
      end
  in
  go [] [] xs1 xs2

let rec mk_simpl_op _strong op l =
  let mk_Ifte_simp e1 e2 e3 =
    mk_simpl_op false Ifte [e1; e2; e3]
  in
  match op, l with (* FIXME : Permuation handling *)
  | GExp gv, [g1;p1] ->
    (*i g1 is necessary of the form g ^ a i*)
    let a = destr_gexp gv g1 in
    let p = norm_field_expr (mk_FMult [a; p1]) in
    mk_gexp gv p
  | GInv, [g1] ->
    let gv = ensure_ty_G g1.e_ty "norm" in
    let a  = destr_gexp gv g1 in
    let p = norm_field_expr (mk_FOpp a) in
    mk_gexp gv p
  | GLog gv, [g1] -> destr_gexp gv g1
  | EMap es, [g1;g2] -> (*i e(g^a,g^b) -> e(g,g)^ab i*)
    let p1 = destr_gexp es.Esym.source1 g1 in
    let p2 = destr_gexp es.Esym.source2 g2 in
    let p = norm_field_expr (mk_FMult [p1; p2]) in
    mk_gexp es.Esym.target p
  | Eq, [e1;e2] when is_False e1            -> norm_expr (mk_Not e2)
  | Eq, [e1;e2] when is_False e2            -> norm_expr (mk_Not e1)
  | Eq, [e1;e2] when is_True e1             -> e2
  | Eq, [e1;e2] when is_True e2             -> e1
  | Eq, [e1;e2] when e_equal e1 e2          -> mk_True
  | Eq, [e1;e2] when ty_equal e1.e_ty mk_Fq ->
    let e = norm_field_expr (mk_FMinus e1 e2) in
    if e_equal e mk_FOne || e_equal e (mk_FOpp mk_FOne) then
      mk_False
    else
      mk_Eq e1 e2 (*i e mk_FZ i*)
  | Eq, [e1;e2] ->
    mk_Eq e1 e2
  | Ifte, [e1;e2;e3] ->
    if is_True e1 then e2
    else if is_False e1 then e3
    else if e_equal e2 e3 then e2
    else if is_FPlus e2 || is_FPlus e3 then (
      let destr_nofail e =
        if is_FPlus e then destr_FPlus e else [e]
      in
      let mk_nofail = function
        | [] -> mk_FZ
        | [e] -> e
        | es  -> mk_FPlus es
      in
      let e2s = destr_nofail e2 in
      let e3s = destr_nofail e3 in
      let common,e2s,e3s = common_diff e2s e3s in
      if common = []
      then norm_ggt (mk_Ifte e1 e2 e3)
      else mk_nofail ((mk_Ifte_simp e1 (mk_nofail e2s) (mk_nofail e3s))::common)
      (*
      log_i (lazy (fsprintf "common: %a, left: %a, right: %a"
                     (pp_list "," pp_exp) common
                     (pp_list "," pp_exp) e2s
                     (pp_list "," pp_exp) e3s));
      *)
    ) else if is_GExp e2 && is_GExp e3 then (
      let (e2_1,e2_2) = destr_GExp e2 in
      let (e3_1,e3_2) = destr_GExp e3 in
      if e_equal e2_1 e3_1 && not (is_GLog e2_2 || is_GLog e3_2)
      then mk_GExp e2_1 (mk_Ifte_simp e1 e2_2 e3_2)
      else norm_ggt (mk_Ifte e1 e2 e3)
    ) else norm_ggt (mk_Ifte e1 e2 e3)
  | Not, [e] ->
    if is_True e then mk_False
    else if is_False e then mk_True
    else
      ( match e.e_node with
        | App(Not,[e]) -> e
        | Quant(q,b,e) -> mk_Quant (neg_quant q) b (norm_expr ~strong:_strong (mk_Not e))
        | _            -> mk_Not e )
  | (        GExp _ | GLog _ | EMap _ | GInv
    | FOpp | FMinus | FInv   | FDiv
    | Eq   | Ifte   | Not)           , _ -> assert false

and mk_simpl_nop strong op l =
  (*i FIXME flattening, for xor and land i*)
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
    (* FIXME: is this really useful?
       We should handle conjunctions manually. *)
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
  | Quant(q,b,e) -> mk_Quant q b (norm_expr ~strong e)
  | Cnst GGen ->  mk_gexp (destr_G e.e_ty) mk_FOne
  | Cnst _ -> e
  | H(h,e) -> norm_ggt (mk_H h (norm_expr ~strong e))
  | App(Perm(ptype1,f),[k1;e1]) -> (
    let k_o_p = key_elem_of_perm_type in
    let k1_norm = norm_expr ~strong k1 and
	e1_norm = remove_tuple_proj (norm_expr ~strong e1) in
    match e1_norm.e_node with
    | App(Perm(ptype2,f),[k2_norm;e2_norm]) (* f(PKey,f_inv(SKey,e)) = e *)
	 when (is_ProjPermKey (k_o_p ptype1) f k1_norm) && ptype1 <> ptype2 &&
                (is_ProjPermKey (k_o_p ptype2) f k2_norm) -> remove_tuple_proj e2_norm 
    | _ -> mk_Perm f ptype1 k1_norm e1_norm )
  | ProjPermKey(ke,kp) ->
     let kp_norm = norm_expr ~strong kp in
     mk_ProjPermKey ke kp_norm
  | Tuple l -> remove_tuple_proj (mk_Tuple (List.map (norm_expr ~strong) l))
  | Proj(i,e) -> mk_proj_simpl i (norm_expr ~strong e)     
  | App (op, l) ->
    if is_field_op op then norm_field_expr e
    else
      let l = List.map (norm_expr ~strong) l in
      mk_simpl_op strong op l
  | Nary (Xor, ess) when is_Prod e.e_ty ->
     let tys = destr_Prod e.e_ty in
     let prod_list_of_e : expr -> expr list = fun e' ->
       (if e'.e_ty <> e.e_ty then failwith "Wrong tuple type");
       match e'.e_node with
       | Tuple l -> (List.map (norm_expr ~strong) l)
       | _ -> let e' = norm_expr ~strong e' in List.mapi (fun i _ -> norm_expr ~strong (mk_Proj i e')) tys in
     let xor_of_tuples : expr list list =
       List.map prod_list_of_e ess in
     let tuples_of_xor = BatList.transpose xor_of_tuples in
     mk_Tuple (List.map (mk_simpl_nop strong Xor) tuples_of_xor)
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
let norm_expr_very_strong e = remove_tuple_proj (norm_expr ~strong:true e)

(*i use norm_expr to check equality modulo equational theory i*)
let e_equalmod e e' = e_equal (norm_expr_very_strong e) (norm_expr_very_strong e')

let norm_expr_abbrev_weak e = abbrev_ggen (norm_expr_weak e)

let norm_expr_abbrev_strong e = abbrev_ggen (norm_expr_strong e)

let norm_expr_nice e = remove_tuple_proj (abbrev_ggen (norm_expr_weak e))

(* In the following, we define a normal form where if-then-else is pushed outwards *)

type 'a nif =
  | Iexpr of 'a (* usually an expression, can be a list of expressions during computations *)
  | Iif   of expr * 'a nif * 'a nif

let rec expr_of_nif ~nf nif =
  match nif with
  | Iexpr(e)         -> nf e
  | Iif(c,nif1,nif2) ->
    let c = nf c in
    let e1 = expr_of_nif ~nf nif1 in
    let e2 = expr_of_nif ~nf nif2 in
    if e_equal e1 e2
    then e1
    else mk_Ifte c e1 e2
  

let rec map_nif ~f nif =
  match nif with
  | Iexpr(e)         -> Iexpr(f e)
  | Iif(c,nif1,nif2) -> Iif(c,map_nif ~f nif1, map_nif ~f nif2)

(* nests nif2 into ni1 *)
let nest_nif (nif1 : expr nif) (nif2 : (expr list) nif) =
  let rec go nif1 =
    match nif1 with
    | Iexpr e1 ->
      map_nif ~f:(fun es2 -> e1 :: es2) nif2
    | Iif(c,nif11,nif22) ->
      Iif(c,go nif11,go nif22)
  in
  go nif1

let nest_nifs nifs =
  let rec go acc = function
    | [] -> acc
    | nif::nifs ->
      go (nest_nif nif acc) nifs
  in
  match L.rev nifs with
  | []        -> assert false
  | nif::nifs -> go (map_nif ~f:(fun e -> [e]) nif) nifs

let napp_nifs ~f nifs =
  match nifs with
  | [] -> Iexpr(f [])
  | _ -> 
    let nif = nest_nifs nifs in
    map_nif ~f nif

let norm_split_if ~nf e =
  let rec go e =
    match e.e_node with
    | V _ | Cnst _ -> Iexpr e
    | Quant(q,b,e)     -> map_nif ~f:(mk_Quant q b) (go e)
    | H(h,e)       -> map_nif ~f:(mk_H h) (go e)
    | ProjPermKey(ke,kp)  -> map_nif ~f:(mk_ProjPermKey ke) (go kp)
    | Proj(i,e)    -> map_nif ~f:(mk_Proj i) (go e)
    | Tuple(es)    -> napp_nifs ~f:mk_Tuple (L.map go es)
    | App(_,_) when is_Ifte e ->
      let (c,e1,e2) = destr_Ifte e in
      let nif1 = go e1 in
      let nif2 = go e2 in
      Iif(c,nif1,nif2)
    | App(o,es)    -> napp_nifs ~f:(fun es -> mk_App o es e.e_ty) (L.map go es)
    | Nary(o,es)   -> napp_nifs ~f:(mk_Nary o) (L.map go es)
  in
  expr_of_nif ~nf (go e)

let norm_expr_conv = norm_split_if ~nf:norm_expr_strong

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

