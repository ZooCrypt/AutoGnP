open Expr
open Type
open Norm
open Rules

module PU = ParserUtil
module Ht = Hashtbl

let parse_ep ht s =
  let pt = Parse.expr s in
  PU.expr_of_parse_expr ht pt

let vc  = Vsym.mk "c" mk_Fq
let vd  = Vsym.mk "d" mk_Fq
let ve  = Vsym.mk "e" mk_Fq
let vi  = Vsym.mk "i" mk_Fq
let vmb = Vsym.mk "mb" mk_G

let _ =
  let ht = Ht.create 20 in
  Ht.add ht "c" vc;
  Ht.add ht "d" vd;
  Ht.add ht "e" ve;
  Ht.add ht "mb" vmb;
  Ht.add ht "i" vi;
  let e = norm_expr (parse_ep ht "g^((log(mb) + c*d*e) / i)") in
  let e' = abbrev_ggen (rewrite_exps (se_of_list [mk_V vc; mk_V vd]) e) in
  Format.printf "before: %a\n" pp_exp e;
  Format.printf "after:  %a\n" pp_exp e'