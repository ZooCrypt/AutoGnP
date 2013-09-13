open Type
open OUnit

let test_type _ =
  let tv = Tyvar.mk "l" in
  Format.printf "tyvar: %a\n" Tyvar.pp tv;

  let ty1 = mk_ty [tv; tv] in
  Hsty.clear (); (* restart the program and load ty1 from storage. *)
  let ty2 = mk_ty [tv; tv] in (* create the same type *)
  (* ty1 not equal ty2*)
  Format.printf "ty1=%a,  ty2=%a,  equal=%b \n" pp_ty ty1 pp_ty ty2 (ty_equal ty1 ty2);
  assert_equal ~msg:"ty1 and ty2 not equal" (ty_equal ty1 ty2) false;

  let ety1 = ty_export ty1 in
  let ety2 = ty_export ty2 in
  (* ety1 equal ety2 *)
  Format.printf "ety1=%a, ety2=%a, equal=%b \n" pp_ty ety1 pp_ty ety2 (ety1 = ety2);
  assert_equal ~msg:"ety1 and ety2 equal" ety1  ety2

let suite = "Type" >::: ["test_type" >:: test_type ]

let _ =
  run_test_tt_main suite