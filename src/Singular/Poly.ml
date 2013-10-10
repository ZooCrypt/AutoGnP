open Expr
open Util

module F = Format

type monom = int list
type coeff = int
type poly = (coeff * monom) list

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

let terms_of_monom m =
  let go acc (_i,k) =
    let vi = mk_V (assert false) in (* FIXME: variable synchronization *)
    match k with 
    | 0 -> acc
    | 1 -> vi::acc
    | k -> replicate k vi @ acc 
  in (List.rev (List.fold_left go [] m))

let term_of_poly p =
  let summand (i,m) =
    let const = match i with
      | i when i > 0 -> mk_FPlus (replicate i mk_FOne)
      | _            -> mk_FOpp (mk_FPlus (replicate (-i) mk_FOne))
    in
    match (i,m) with
    | (_,[]) -> const
    | (1,_)  -> mk_FMult (terms_of_monom m)
    | (-1,_) -> mk_FOpp (mk_FMult (terms_of_monom m))
    | _      -> mk_FMult (const::terms_of_monom m)
  in mk_FPlus (List.map summand p)
