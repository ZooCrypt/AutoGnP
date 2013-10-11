open Singular
open Expr
open ExprSyntax
open Type
open Util

let main =
  let vs = Vsym.mk "x" mk_Fq in
  let v = mk_V vs in
  let h = Hsym.mk "h" mk_G mk_Fq in
  let e =  ((v +: (fint 2)) /: ((fpow v 2) -: (fint 4))) +: mk_H h mk_GGen in
  let (e',_c,_hv) = abstract_non_field (fun e -> e) e in
  F.printf "%a\n" pp_exp e;
  F.printf "%s\n" (string_of_fexp e');
  print_newline ();
  F.printf "%a\n" pp_exp (norm (fun e -> e) e)
