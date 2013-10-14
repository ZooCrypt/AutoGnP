open Type
open Expr

module PU = ParserUtil
module Ht = Hashtbl

let f () =
  let pt = 
    Parse.ty "(BS_l1 * (Bool * Bool * BS_l2))"
  in Format.printf "%a\n\n" pp_ty (PU.ty_of_parse_ty pt)

let test_ep ht s =
  let pt = Parse.expr s in
  Format.printf "%a\n\n" pp_exp (PU.expr_of_parse_expr ~ht pt)

let _ = test_ep (Ht.create 20)
                "not (true ? false : true /\\ true)"

let _ = test_ep (Ht.create 20)
                "(1,1)"

let _ =
  let vc  = Vsym.mk "c" mk_Fq in
  let vd  = Vsym.mk "d" mk_Fq in
  let ve  = Vsym.mk "e" mk_Fq in
  let vmb = Vsym.mk "mb" mk_GT in  
  let ht = Ht.create 20 in
  Ht.add ht "c" vc;
  Ht.add ht "d" vd;
  Ht.add ht "e" ve;
  Ht.add ht "mb" vmb;
  test_ep ht "mb * e(g,g)^(c*d*e) * mb"
