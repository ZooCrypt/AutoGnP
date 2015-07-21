(*open Abbrevs*)
open Expr
open ExprUtils
(*open Type*)
open Util
module G = Game
open Syms
open CoreTypes
module Ht = Hashtbl
module PU = ParserUtil
(*open Nondet*)

module CR = CoreRules

let rbad which_bad p vsx_name vmap ts ju =  
  (* fail_if_occur vsx ju "rbad"; FIXME : why is this needed ?*)
  let se = ju.ju_se in
  match G.get_se_ctxt se p with
  | G.GLet(vs,e'), se_ctxt when is_H e' ->
     let h,e = destr_H e' in
     let vsx = if (Ht.mem vmap (Unqual,vsx_name)) then
                 Ht.find vmap (Unqual,vsx_name) else
                 PU.create_var vmap ts Unqual vsx_name e.Expr.e_ty in
     if (Vsym.S.mem vsx (G.expr_vars e)) then (* checking vsx not in fv(e) *)
       tacerror "Error, var \'%a\' appears in expr \'%a\'" Vsym.pp vsx pp_exp e;     
     if not (Hsym.is_ro h) then
       tacerror "Error, the function \'%a\' is not a random oracle" Hsym.pp h;

     
     let cmds = [ G.GSamp(vs, (e'.e_ty,[]) )] in
     (* ju1 is ju with a random sampling instead of the hash call *)
     let ju1 = {ju with ju_se = (G.set_se_ctxt cmds se_ctxt) } in

     (* Checking that h is only used here *)
     let all_other_hash_calls_args = Se.union
                              (G.gdef_all_hash_calls_h h se_ctxt.G.sec_left)
                              (G.gdef_all_hash_calls_h h se_ctxt.G.sec_right) in
     if (Se.mem e all_other_hash_calls_args) then
       tacerror "Error, there cannot be other \'%a\' calls in main game querying the same expression \'%a\'" Hsym.pp h pp_exp e;
     let create_ju ei =
       { ju_pr = Pr_Succ ;
         ju_se = { ju1.ju_se with G.se_ev =
                                    { G.ev_quant = G.Forall;
                                      G.ev_binding = [];
                                      G.ev_expr = (mk_Eq e ei) } } } in
     let check_other_hc_expr_eq_jus = List.rev (Se.fold
                                     ( fun ei jus -> (create_ju ei)::jus )
                                     all_other_hash_calls_args []) in
     let bad_ev_expr = mk_Eq (mk_V vsx) e and
         bad_ev_binding = ([vsx],Oracle.mk_RO(h)) in
     let bad_n,ju2 = match which_bad with
     (* ju2 is ju1 where event = bad_event + main_event when UpToBad, 
                              or bad_event only when CaseDist *)
       | PU.UpToBad ->
          let conj_ev = { G.ev_quant   = G.Exists;
                          G.ev_binding = bad_ev_binding :: se.G.se_ev.G.ev_binding;
                          G.ev_expr    = insert_Land bad_ev_expr se.G.se_ev.G.ev_expr } in
          2, {ju_pr = Pr_Succ; ju_se = {ju1.ju_se with G.se_ev = conj_ev} }
       | PU.CaseDist ->
          let bad_ev = { G.ev_quant   = G.Exists;
                         G.ev_binding = [bad_ev_binding];
                         G.ev_expr    = bad_ev_expr } in
          1, {ju_pr = Pr_Succ; ju_se = {ju1.ju_se with G.se_ev = bad_ev} }
     in
     CoreTypes.Rbad(bad_n,p,vsx), ju1::ju2::check_other_hc_expr_eq_jus
  | _ -> tacerror "cannot apply \'bad\' rule at pos %i\n<< \'Let var = H(expr)\' required >>\n(remember you can use the \'abstract\' rule to fold a hash call into a variable)." (p+1)
     



(* TEST FUNCTION -- NOT VALID *)
let rbad_oracle which_bad opos vsx_name ts ju =   
  (* fail_if_occur vsx ju "rbad"; FIXME : why is this needed ?*)
  let se = ju.ju_se in
  let vmap = G.vmap_in_orcl se opos in
  match G.get_se_octxt se opos with
  | G.LLet(vs,e'), se_octxt when is_H e' ->
     let h,e = destr_H e' in
     let vsx = if (Ht.mem vmap (Unqual,vsx_name)) then
                 Ht.find vmap (Unqual,vsx_name) else
                 PU.create_var vmap ts Unqual vsx_name e.Expr.e_ty in
     if (Vsym.S.mem vsx (G.expr_vars e)) then (* checking vsx not in fv(e) *)
       tacerror "Error, var \'%a\' appears in expr \'%a\'" Vsym.pp vsx pp_exp e;     
     if not (Hsym.is_ro h) then
       tacerror "Error, the function \'%a\' is not a random oracle" Hsym.pp h;

     (* FIXME Checking that h is only used here 
     let all_other_hash_calls = Hsym.S.union
                              (gdef_all_hash_calls se_ctxt.sec_left)
                              (gdef_all_hash_calls se_ctxt.sec_right) in
     if (Hsym.S.mem h all_other_hash_calls) then
       tacerror "Error, there must not be other \'%a\' calls in main game to apply the bad rule" Hsym.pp h; *)
     
     let cmds = [ G.LSamp(vs, (e'.e_ty,[]) )] in
     let ju1 = {ju with ju_se = (G.set_se_octxt cmds se_octxt) } in
     let bad_ev_expr = mk_Eq (mk_V vsx) e and
         bad_ev_binding = ([vsx],Oracle.mk_RO(h)) in
     ( match which_bad with
       | PU.UpToBad ->
          let conj_ev = { G.ev_quant   = G.Exists;
                          G.ev_binding = bad_ev_binding :: se.G.se_ev.G.ev_binding;
                          G.ev_expr    = insert_Land bad_ev_expr se.G.se_ev.G.ev_expr } in
          let ju2 = {ju with ju_se = {se with G.se_ev = conj_ev} } in
          CoreTypes.RbadOracle(2,opos,vsx), [ju1;ju2]
       | PU.CaseDist ->
          let bad_ev = { G.ev_quant   = G.Exists;
                         G.ev_binding = [bad_ev_binding];
                         G.ev_expr    = bad_ev_expr } in
          let ju2 = { ju_pr = Pr_Succ;
                      ju_se = {ju1.ju_se with G.se_ev = bad_ev} } in
          CoreTypes.RbadOracle(1,opos,vsx), [ju1;ju2] )
  | _ ->
     tacerror "Cannot apply BAD rule : \'Let var(s) = H(expr)\' required."              
(*
let rbad_old p vsx ju =
  fail_if_occur vsx ju "rbad";
  let se = ju.ju_se in
  match get_ju_ctxt se p with
  | GLet(vs,e'), ctxt when is_H e' ->
    let h,e = destr_H e' in
    if not (Hsym.is_ro h) then
      tacerror "the function %a is not a random oracle" Hsym.pp h;
    (*i TODO CHECK THAT h is only used here, and that call are guarded in
       oracle i *)
    let i = [GSamp(vs,(e'.e_ty,[]))] in
    let ju1 = set_ju_ctxt i ctxt in
    let vx = mk_V vsx in
    let ev = mk_Exists e vx [vsx,h] in
    let ju2 = { ju1 with ju_ev = ev } in
    Rbad(p,vsx), [ju1;ju2]
  | _ ->
    tacerror "can not apply bad rule"
 *)
