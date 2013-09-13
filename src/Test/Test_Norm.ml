open Norm
open Expr
open Type
open OUnit


let test_norm _ =
  let tv = Tyvar.mk "k" in
  let ty = mk_ty [tv] in
  let hs = Hsym.mk "H" ty ty in

  let h = mk_H hs (mk_Xor (mk_Z ty) (mk_Z ty)) in
  let nh = norm h in
  Format.printf "exp: %a\n" pp_exp nh;
  assert_equal ~msg:"norm h" (e_equal nh (mk_H hs (mk_Z ty))) true

let suite = "Norm" >::: ["test_norm" >:: test_norm ]

let _ =
  run_test_tt_main suite
