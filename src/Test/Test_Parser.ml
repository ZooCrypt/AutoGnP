(* open Type *)
(* open Expr *)

module PU = ParserUtil
module Ht = Hashtbl

(*
let f () =
  let pt = 
    Parse.ty "(BS_l1 * (Bool * Bool * BS_l2))"
  in Format.printf "%a\n\n" pp_ty (PU.ty_of_parse_ty pt)

let test_ep ht s =
  let pt = Parse.expr s in
  Format.printf "%a\n\n" pp_exp (PU.expr_of_parse_expr ~ht pt)

let f _ = test_ep (Ht.create 20)
                "not (true ? false : true /\\ true)"

let f _ = test_ep (Ht.create 20) "(1,1)"

let f _ =
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
*)

let test_theory s =
  let pt = Parse.theory s in
  List.fold_left (fun ps i -> PU.handle_instr ps i) PU.mk_ps pt

let ps = test_theory
"adversary A1 : () -> Fq.\
adversary A2 : (G * G * G) -> (GT * GT).\
adversary A3 : (GT * G * G) -> Bool.\
oracle Kg : Fq -> (G * G).\
prove \
[ i' <- A1();\
  c <-$ Fq;\
  d <-$ Fq;\
  e <-$ Fq;\
  h <-$ Fq;\
  b <-$ Bool;\
  (m0,m1) <- A2(g^c, g^d, g^h);\
  let mb = (b?m0:m1);\
  b' <- A3(mb * e(g,g)^((c*d)*e), g^e, g^(e*(d*i' + h))) with\
    Kg(i) = [ (g^(c*d + r*(d*i + h)), g^r) | not (i=i'), r <-$ Fq]\
] : b = b'. \
print_goals : start.
rnorm.
print_goals : after_norm."