open Expr
open Type
open OUnit

let test_expr _ =
  let tv = Tyvar.mk "k" in
  let ty = mk_ty [tv] in
  let hs = Hsym.mk "H" ty ty in
  let h = mk_H hs (mk_Z ty) in
  Format.printf "exp: %a\n" pp_exp h;
  assert_equal ~msg:"e_equal reconstruct" (e_equal h (mk_H hs (mk_Z ty))) true

let suite = "Expr" >::: ["test_ident" >:: test_expr ]

let _ =
  run_test_tt_main suite