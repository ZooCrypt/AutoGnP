open Expr
open Util

module F = Format

type var = int
type monom = (var * int) list (* m_i = x_i^j_i *)
type coeff = int
type poly = (coeff * monom) list (* a_1 * m_1 + .. + a_k * m_k *)

let terms_of_monom bindings (m : monom) =
  let go acc (i,k) =
    let e = match massoc i bindings with
      | Some e -> e
      | None   -> failwith "terms_of_monom: unexpected variable returned by Singular"
    in replicate k e @ acc 
  in List.rev (List.fold_left go [] m)

let term_of_poly bindings p =
  let const i = match i with
    | 0            -> mk_FZ
    | i when i > 0 -> mk_FPlus (replicate i mk_FOne)
    | _            -> mk_FOpp (mk_FPlus (replicate (-i) mk_FOne))
  in
  let summand (i,m) = match i, terms_of_monom bindings m with
    | _,[]   -> const i
    | 1,mes  -> mk_FMult mes
    | -1,mes -> mk_FOpp (mk_FMult mes)
    | _,mes  -> mk_FMult (const i::mes)
  in mk_FPlus (List.map summand p)

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

