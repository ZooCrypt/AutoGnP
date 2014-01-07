(* Internal module for Singular interface *)
open Expr
open Util

module F = Format
module S = String
module L = List

(* ----------------------------------------------------------------------- *)
(** {1 Define and check normal-form for field-expressions } *)

(* Field-expression in normal-form are captured by the following grammar:
   fe ::= fe0 / fe0 | fe0
   fe0 ::= mon | mon + .. + mon
   mon ::= - mon0 | mon0
   mon0 ::= NAT
         |  NAT * NFE * .. * NFE
         |  NFE * ... * NFE
         |  NFE
*)
let rec is_norm_field_exp e =
  if is_FDiv e then
    let (e1,e2) = destr_FDiv e in
    is_fe0 e1 && is_fe0 e2
  else is_fe0 e

and is_fe0 e =
  if is_FPlus e
  then L.for_all is_mon (destr_FPlus e)
  else is_mon e

and is_mon e =
  if is_FOpp e
  then is_mon0 (destr_FOpp e)
  else is_mon0 e

and is_mon0 e =
  if is_FMult e then
    (match destr_FMult e with
     | _::_ as xs ->
       let (ys,zs) = L.partition is_FNat xs in
       (match ys with
        | [_] | [] -> L.for_all (fun x -> not (is_field_exp x)) zs
        | _::_::_ -> false)
     | _ -> false)
  else (is_FNat e || not (is_field_exp e))

(* ----------------------------------------------------------------------- *)
(** {2 Field expressions as polynomials (fe = f / g) } *)

type var = int
type 'a monom = ('a * int) list (* m_i = x_i^j_i *)
type coeff = int
type 'a poly = (coeff * 'a monom) list (* a_1 * m_1 + .. + a_k * m_k *)

let map_poly f p =
  L.map (fun (c,m) -> (c, L.map (fun (x,e) -> (f x,e)) m)) p

let exps_of_monom (m : 'a monom) =
  let go acc (x,k) = replicate_r acc k x in 
  let l = L.fold_left go [] m in
  L.sort e_compare l 

let exp_of_poly p =
  let summand (i,m) = match i, exps_of_monom m with
    | _,[]   -> if i < 0 then mk_FOpp (mk_FNat (-i)) else mk_FNat i
    | 1,mes  -> mk_FMult mes
    | -1,mes -> mk_FOpp (mk_FMult mes)
    | _,mes  -> 
      assert (i <> 0 && i <> 1 && i <> -1);
      if i > 0 then mk_FMult (mk_FNat i    :: mes)
      else mk_FOpp (mk_FMult (mk_FNat (-i) :: mes))        
  in
  let s = L.map summand p in
  let e = mk_FPlus (L.sort e_compare s) in
  if (not (is_norm_field_exp e)) then F.printf "ERROR: %a\n\n%!" pp_exp e;
  assert (is_norm_field_exp e);
  e

(* takes a term in normal form and returns the corresponding polynomial 
   fails if given term is not in normal-form *)
let polys_of_field_expr e =
  let rec conv_fe0 e =
    if is_FPlus e
    then L.map conv_mon (destr_FPlus e)
    else [ conv_mon e ]
  and conv_mon e =
    if is_FOpp e
    then conv_mon0 (fun x -> - x) (destr_FOpp e)
    else conv_mon0 (fun x -> x) e
  and conv_mon0 minv e =
    let add_exponents es = L.map (fun e -> (e,1)) es in
    if is_FMult e then
      (match destr_FMult e with
       | _::_ as xs->
           let (ys,zs) = L.partition is_FNat xs in
           begin match ys with
           | [x] ->
               (match x.e_node with
                | Cnst(FNat n) -> (minv n, add_exponents zs)
                | _ -> assert false)
           | [] -> (minv 1, add_exponents xs)
           | _::_::_ -> assert false
           end
       | _ -> assert false)
    else
      (match e.e_node with
       | Cnst(FNat n) -> (minv n, [])
       | _            -> (minv 1, add_exponents [e]))
  in
  if is_FDiv e then
    let (e1,e2) = destr_FDiv e in
    (conv_fe0 e1, Some(conv_fe0 e2))
  else (conv_fe0 e, None)

(* ----------------------------------------------------------------------- *)
(** {3 For debugging only } *)

let string_of_monom m =
  let go acc (i,k) =
    let vi = F.sprintf "x%i" i in
    match k with 
    | 0 -> acc
    | 1 -> vi::acc
    | k -> (vi^(F.sprintf "^%i" k))::acc
  in S.concat "*" (L.rev (L.fold_left go [] m))

let _string_of_poly p = 
  S.concat " + "
    (L.map (fun (i,m) ->  (if i = 1 then "" else string_of_int i)
                            ^(string_of_monom m)) p)

let factor_out a p =
  lefts_rights
    (L.map
      (fun (c,es) ->
         match L.partition (fun (e,_) -> e_equal e a) es with
         | ([(_,1)],others) -> Left(c,others)
         | ([],others)      -> Right(c,others)
         | _ -> failwith (fsprintf "cannot factor out %a" pp_exp a |> fsget))
      p)
