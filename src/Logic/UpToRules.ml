(*open Abbrevs*)
open Expr
open ExprUtils
(*open Type*)
open Util
open Game
open Syms
open CoreTypes
module Ht = Hashtbl
module PU = ParserUtil
(*open Nondet*)

module CR = CoreRules
           
let rbad p vsx_name vmap ts ju = (* TODO : Add boolean flag to work with Fail2 rule *)
  
  (* fail_if_occur vsx ju "rbad"; FIXME : why is this needed ?*)
  let se = ju.ju_se in
  match get_se_ctxt se p with
  | GLet(vs,e'), se_ctxt when is_H e' ->
     let h,e = destr_H e' in
     let vsx = if (Ht.mem vmap (Unqual,vsx_name)) then
                 Ht.find vmap (Unqual,vsx_name) else
                 PU.create_var vmap ts Unqual vsx_name e.Expr.e_ty in
     if (Vsym.S.mem vsx (expr_vars e)) then (* checking vsx not in fv(e) *)
       tacerror "Error, var \'%a\' appears in expr \'%a\'" Vsym.pp vsx pp_exp e;     
     if not (Hsym.is_ro h) then
       tacerror "Error, the function \'%a\' is not a random oracle" Hsym.pp h;

     (* Checking that h is only used here *)
     let all_other_hash_calls = Hsym.S.union (* FIXME : all OR global ? *)
                              (gdef_global_hash_calls se_ctxt.sec_left)
                              (gdef_global_hash_calls se_ctxt.sec_right) in
     if (Hsym.S.mem h all_other_hash_calls) then
       tacerror "Error, there must not be other \'%a\' calls in main game to apply the bad rule" Hsym.pp h;
    
     (*i TODO : CHECK THAT calls are guarded in oracle i*)
     
     let cmds = [ GSamp(vs, (e'.e_ty,[]) )] in
     let ju1 = {ju with ju_se = (set_se_ctxt cmds se_ctxt) } in
     let ev = { ev_quant   = Exists;
                ev_binding = [[vsx],Oracle.RO(h)];
                ev_expr    = mk_Eq (mk_V vsx) e  } in
     let ju2 = { ju_pr = Pr_Succ;
                 ju_se = {ju1.ju_se with se_ev = ev} } in
     Rbad(p,vsx), [ju1;ju2]
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
