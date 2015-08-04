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
  let p_ctxt =
    try G.get_se_ctxt se p
    with
      Failure s -> tacerror "Invalid position %i :\n%s" (p+1) s
  in
  match p_ctxt with
  | G.GLet(vs,e'), se_ctxt when is_H e' ->
    let h,e = destr_H e' in
    let vsx =
      if (Ht.mem vmap (Unqual,vsx_name))
      then Ht.find vmap (Unqual,vsx_name)
      else PU.create_var vmap ts Unqual vsx_name e.Expr.e_ty
    in
    if (Vsym.S.mem vsx (G.expr_vars e)) then
      tacerror "Error, var '%a' appears in expr '%a'" Vsym.pp vsx pp_exp e;
    if not (Hsym.is_ro h) then
      tacerror "Error, the function '%a' is not a random oracle" Hsym.pp h;
    if (Hsym.is_lkup h) then
      tacerror "Error, 'bad' rule cannot be applied to the oracle lookup '%a'" Hsym.pp h;
     
    let cmds = [ G.GSamp(vs, (e'.e_ty,[]) )] in
    (* ju1 is ju with a random sampling instead of the hash call *)
    let ju1 = {ju with ju_se = (G.set_se_ctxt cmds se_ctxt) } in

    (* Checking that h is only used here *)
    let all_other_hash_calls_args =
      Se.union
        (G.gdef_all_hash_args h se_ctxt.G.sec_left)
        (G.gdef_all_hash_args h se_ctxt.G.sec_right)
    in
     if (Se.mem e all_other_hash_calls_args) then
       tacerror "Error, there cannot be other '%a' calls querying the expression '%a'" Hsym.pp h pp_exp e;
     let create_ju = match which_bad with
       | PU.CaseDist -> fun ei ->
         { ju_pr = Pr_Succ ;
           ju_se = { ju1.ju_se with G.se_ev =
                                      { G.ev_quant = G.EvForall;
                                        G.ev_binding = [];
                                        G.ev_expr = (mk_Eq e ei) } } }
       | PU.UpToBad -> fun ei ->
         { ju_pr = Pr_Succ ;
           ju_se = { ju.ju_se with G.se_ev =
                               { se.G.se_ev with
                                 G.ev_expr = 
                                   mk_Land [mk_Eq e ei; se.G.se_ev.G.ev_expr]}}}
     in
     let check_other_hc_expr_eq_jus =
       Se.fold (fun ei jus -> (create_ju ei)::jus) all_other_hash_calls_args []
       |> List.rev
     in
     let bad_ev_expr = mk_Eq (mk_V vsx) e in
     let bad_ev_binding = ([vsx],Oracle.mk_RO(h)) in
     let bad_n,ju2 = match which_bad with
     (* ju2 is ju1 where event = bad_event + main_event when UpToBad, 
                              or bad_event only when CaseDist *)
       | PU.UpToBad ->
          let conj_ev = { G.ev_quant   = G.EvExists;
                          G.ev_binding = bad_ev_binding :: se.G.se_ev.G.ev_binding;
                          G.ev_expr    = mk_Land [bad_ev_expr; se.G.se_ev.G.ev_expr] }
          in
          2, {ju_pr = Pr_Succ; ju_se = {ju.ju_se with G.se_ev = conj_ev} }
       | PU.CaseDist ->
          let bad_ev = { G.ev_quant   = G.EvExists;
                         G.ev_binding = [bad_ev_binding];
                         G.ev_expr    = bad_ev_expr }
          in
          1, {ju_pr = Pr_Succ; ju_se = {ju1.ju_se with G.se_ev = bad_ev} }
     in
     CoreTypes.Rbad(bad_n,p,vsx), ju1::ju2::check_other_hc_expr_eq_jus
  | _ ->
    tacerror
      ("cannot apply 'bad' rule at pos %i\n<< 'let var = H(expr)\' required:"
       ^^">>\n(note that the 'abstract' rule can be used to fold a hash call into a variable).")
      (p+1)
     
let t_bad which_bad p vsx_name vmap ts ju =
  CR.prove_by (rbad which_bad p vsx_name vmap ts) ju
           
let rcheck_hash_args opos ts ju =
  let se = ju.ju_se in
  let bad_position ?s () =
    let (i,j,k,_) = opos in
    tacerror "Invalid guard position (%i,%i,%i)\n%s"
      (i+1) (j+1) (k+1)
      (match s with Some s -> "<< " ^ s ^ " >>" | _ -> "")
  in
  let gctxt =
    try G.get_se_octxt se opos with Failure s -> bad_position ~s ()
  in
  match gctxt with
  | (G.LGuard(eq) as lguard), se_octxt ->
     if not (is_SomeQuant eq) then
       tacerror "Error, '%a' is not a quantified expression" pp_exp eq;
     let _,(vs,o),eq = ExprUtils.destr_Quant eq in
     let ve,e =
       try ExprUtils.destr_Eq eq
       with
         ExprUtils.Destr_failure _ ->
           tacerror "Error, expected 'v = expr' expression, with v bound in L_%a" Oracle.pp o
     in
     let o =
       try Oracle.destr_as_Hsym_t o
       with
         Oracle.Destr_failure _ ->
           tacerror "Error, '%a' is not a random oracle" Oracle.pp o
     in
     let o_lkup = Mstring.find (Hsym.to_string o) ts.TheoryTypes.ts_lkupdecls in
     if not (List.exists (fun v -> e_equal ve (mk_V v)) vs) then
       tacerror "Error, expected 'v = expr' expression, with v bound in L_%a" Hsym.pp o;
     let seoc_cright = se_octxt.G.seoc_cright in
     let to_lkup = function
       | (h,e') when (Hsym.equal h o && e_equal e e') -> o_lkup
       | (h,_) -> h
     in
     let seoc_cright = G.subst_lkup_lcmds to_lkup seoc_cright in
     let se_octxt = {se_octxt with G.seoc_cright} in
     CoreTypes.Rcheck_hash_args opos,[{ju with ju_se = G.set_se_octxt [lguard] se_octxt}]

  | _ -> bad_position ()

let t_check_hash_args opos ts ju =
  CR.prove_by (rcheck_hash_args opos ts) ju
