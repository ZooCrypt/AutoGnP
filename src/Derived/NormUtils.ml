(* * Non-core functions for normal form *)

(* ** Imports *)

open Expr
open ExprUtils
open Norm
open Type

(* ** remove 
 * ----------------------------------------------------------------------- *)

let rm_tuple_proj e es =
  match es with
  | e1::es ->
    begin
      try
        let i, e2 = destr_Proj e1 in
        if i <> 0 then raise Not_found;
        if List.length es + 1 <> List.length (destr_Prod_exn e2.e_ty) then
          raise Not_found;
        List.iteri (fun i e ->
          let i',e' = destr_Proj e in
          if i + 1 <> i' || not (equal_expr e2 e') then raise Not_found) es;
        e2
      with Not_found | Destr_failure _ -> e
    end
  | _ -> e

(* FIXME: clarify name *)
let rec remove_tuple_proj e =
  let e = e_sub_map remove_tuple_proj e in
  match e.e_node with
  | Tuple es -> rm_tuple_proj e es
  | _ -> e

(* ** ???
 * ----------------------------------------------------------------------- *)

let rec abbrev_ggen e =
  let e = e_sub_map abbrev_ggen e in
  match e.e_node with
  | App(GExp _,[a;b]) ->
    if is_GGen a then (
       if equal_expr b mk_FOne then a
       else if is_GLog b then destr_GLog b
      else e)
    else e
  | _ -> e

let norm_expr_nice e = remove_tuple_proj (abbrev_ggen (norm_expr_weak e))

(*
let norm_expr_weak e = norm_expr ~strong:false e

let norm_expr_strong e = remove_tuple_proj (norm_expr ~strong:true e)

let norm_expr_abbrev_weak e = abbrev_ggen (norm_expr_weak e)

let norm_expr_abbrev_strong e = abbrev_ggen (norm_expr_strong e)


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
    if equal_expr e1 e2
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
 *)

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
