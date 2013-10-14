(* Internal module for Singular interface *)
open Expr
open Util

module F = Format

type var = int
type monom = (var * int) list (* m_i = x_i^j_i *)
type coeff = int
type poly = (coeff * monom) list (* a_1 * m_1 + .. + a_k * m_k *)

let terms_of_monom hv (m : monom) =
  let go acc (i,k) =
    let e = try Hashtbl.find hv i with Not_found -> assert false in
    replicate_r acc k e in 
  let l = List.fold_left go [] m in
  List.sort e_compare l 

(* TODO move this *)
let mk_FTwo = mk_FPlus [mk_FOne; mk_FOne]

let rec of_pos_int n = 
  if n <= 1 then mk_FOne 
  else 
    let q = n lsr 1 in
    let r = n mod 2 in
    let tq = mk_FMult [mk_FTwo; of_pos_int q] in
    if r = 1 then mk_FPlus [tq; mk_FOne]
    else tq 

let of_int n = 
  if n = 0 then mk_FZ
  else if n > 0 then of_pos_int n
  else mk_FOpp (of_pos_int (-n))

let term_of_poly hv p =
  let summand (i,m) = match i, terms_of_monom hv m with
    | _,[]  -> of_int i
    | 1,mes  -> mk_FMult mes
    | -1,mes -> mk_FOpp (mk_FMult mes)
    | _,mes -> 
      assert (i <> 0);
      if i > 0 then mk_FMult (of_pos_int i    :: mes)
      else mk_FOpp (mk_FMult (of_pos_int (-i) :: mes))        
  in
  let s = List.map summand p in
  mk_FPlus (List.sort e_compare s)

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

