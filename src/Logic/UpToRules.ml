(*open Abbrevs*)
open Expr
open ExprUtils
(*open Type*)
open Util
open Game
open Syms
open CoreTypes
(*open Nondet*)

module CR = CoreRules

type oracle =
  | RO of Hsym.t
  | O of Osym.t
           
let rbad p vsx ju =
  (* fail_if_occur vsx ju "rbad"; WHY  IS THIS NEEDED ?*)
  let se = ju.ju_se in
  match get_se_ctxt se p with
  | GLet(vs,e'), se_ctxt when is_H e' ->
    let h,e = destr_H e' in
    if not (Hsym.is_ro h) then
      tacerror "the function %a is not a random oracle" Hsym.pp h;
    (*i TODO CHECK THAT h is only used here, and that call are guarded in
       oracle i*)
    
    let cmds = [GSamp(vs,(e'.e_ty,[]))] in
    let ju1 = {ju with ju_se = (set_se_ctxt cmds se_ctxt) } in
    let ev = { ev_quant   = Exists;
               ev_binding = [[vsx],Oracle.RO(h)];
               ev_expr    = e } in
    let ju2 = { ju1 with ju_se = {se with se_ev = ev} } in
   Rbad(p,vsx), [ju1;ju2]
  | _ ->
    tacerror "Cannot apply BAD rule : \'Let var(s) = H(expr)\' required."

(*
let rbad_old p vsx ju =
  fail_if_occur vsx ju "rbad";
  let se = ju.ju_se in
  match get_se_ctxt se p with
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
