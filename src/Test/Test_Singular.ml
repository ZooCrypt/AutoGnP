open Singular
open Expr
open Type
open Util

let main =
  let vs = Vsym.mk "x" mk_Fq in
  let v = mk_V vs in
  let h = Hsym.mk "h" mk_G mk_Fq in
  let num n = mk_FPlus (replicate n mk_FOne) in
  let pow e n = mk_FMult (replicate n e) in
  let (/:) = mk_FDiv in
  let (-:) = mk_FMinus in
  let (+:) a b = mk_FPlus [a;b] in
  let (&:) a b = mk_FMult [a;b] in
  let e =  ((v +: (num 2)) /: ((pow v 2) -: (num 4))) +: mk_H h mk_GGen in
  let (e',bindings) = abstract_non_field e in
  F.printf "%a\n" pp_exp e;
  F.printf "%s\n" (string_of_fexp e');
  print_newline ();
  F.printf "%a\n" pp_exp (norm e)