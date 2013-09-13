open OUnit

let test_ident _ =
  let i1 = Id.mk "foo" in
  let i2 = Id.mk "foo" in
  assert_equal ~msg:"name equal" (Id.name i1) (Id.name i2);
  assert_equal ~msg:"idents not equal" false (Id.equal i1 i2);
  let ei1 = Id.export i1 in
  let ei2 = Id.export i2 in
  assert_equal ~msg:"exported not equal" false (ei1 = ei2)

let suite = "Util" >::: ["test_ident" >:: test_ident ]

let _ =
  run_test_tt_main suite