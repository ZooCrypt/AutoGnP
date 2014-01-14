open Norm
open Type
open Expr
open DeducField
open OUnit

let vx = Vsym.mk "x" mk_Fq
let vy = Vsym.mk "y" mk_Fq
let vz = Vsym.mk "z" mk_Fq
let (x,y,z) = (mk_V vx, mk_V vy, mk_V vz)

let p1 = mk_V (Vsym.mk "p1" mk_Fq)
let p2 = mk_V (Vsym.mk "p2" mk_Fq)
let p3 = mk_V (Vsym.mk "p3" mk_Fq)
let p4 = mk_V (Vsym.mk "p4" mk_Fq)

let eval_ctx known ctx =
  let m = List.fold_left (fun m (k,e) -> Me.add k e m) Me.empty known in
  norm_expr (e_subst m ctx)

let test1 _ =
  let a   = mk_FPlus [x] in
  let b   = mk_FPlus [x;z] in  
  let sec = mk_FPlus [z] in
  let known = [ (p1,a); (p2,b) ] in
  let ctx = solve_fq known sec in
  assert_equal ~msg:"test1: solution valid" (eval_ctx known ctx) sec

let test2 _ =
  let a   = mk_FPlus [x;y] in
  let b   = mk_FPlus [x;z] in
  let sec = mk_FPlus [z] in
  let known = [ (p1,a); (p2,b) ] in
  assert_raises ~msg:"test2: no solution" Not_found (fun () -> solve_fq known sec)

let test3 _ = 
  let a   = mk_FPlus [x] in
  let b   = mk_FPlus [x;z] in  
  let c   = mk_FPlus [y] in  
  let sec = mk_FMult [z;y] in
  let known = [ (p1,a); (p2,b); (p3,c) ] in
  let ctx = solve_fq known sec in
  assert_equal ~msg:"test3: solution valid" (eval_ctx known ctx) sec

let suite =
  "Solve_fq" >::: [ "test_solve_fq_1" >:: test1
                  ; "test_solve_fq_2" >:: test2
                  ; "test_solve_fq_3" >:: test3 ]

let _ = run_test_tt_main suite