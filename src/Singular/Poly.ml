(* Internal module for Singular interface *)
open Expr
open Util

module F = Format

type var = int
type 'a monom = ('a * int) list (* m_i = x_i^j_i *)
type coeff = int
type 'a poly = (coeff * 'a monom) list (* a_1 * m_1 + .. + a_k * m_k *)

let map_poly f p =
  List.map (fun (c,m) -> (c, List.map (fun (x,e) -> (f x,e)) m)) p

let terms_of_monom (m : 'a monom) =
  let go acc (x,k) = replicate_r acc k x in 
  let l = List.fold_left go [] m in
  List.sort e_compare l 

let term_of_poly p =
  let summand (i,m) = match i, terms_of_monom m with
    | _,[]   -> mk_FNat i
    | 1,mes  -> mk_FMult mes
    | -1,mes -> mk_FOpp (mk_FMult mes)
    | _,mes -> 
      assert (i <> 0 && i <> 1 && i <> -1);
      if i > 0 then mk_FMult (mk_FNat i    :: mes)
      else mk_FOpp (mk_FMult (mk_FNat (-i) :: mes))        
  in
  let s = List.map summand p in
  mk_FPlus (List.sort e_compare s)

(* takes a term in normal form and returns the corresponding polynomial 
   fails if given term is not in normal-form *)
let poly_of_term _ = failwith "not implemented"

(* for debugging only *)

let string_of_monom m =
  let go acc (i,k) =
    let vi = F.sprintf "x%i" i in
    match k with 
    | 0 -> acc
    | 1 -> vi::acc
    | k -> (vi^(F.sprintf "^%i" k))::acc
  in String.concat "*" (List.rev (List.fold_left go [] m))

let string_of_poly p = 
  String.concat " + " (List.map (fun (i,m) ->
                                   (if i = 1 then "" else string_of_int i)
                                   ^(string_of_monom m)) p)

