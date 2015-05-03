(*s Decisional and computational assumptions *)

(*i*)
open Abbrevs
open Util
open Game
open Expr
open ExprUtils
open Syms

let log_t ls = mk_logger "Logic.Core" Bolt.Level.TRACE "Assumption" ls
let _log_d ls = mk_logger "Logic.Core" Bolt.Level.DEBUG "Assumption" ls
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Decisional assumptions} *)

(*i For simplicity, we restrict ourselves to assumptions to be of the form
     \verb!r1 <-$ D1; ...; rn <-$ Dn; (vs1) <- A1(e1); ...; (vsk) <- Ak(ek);!
   where 'Di' might be an excepted distribution [*].
   Then the right assumption has the form
     \verb!r1' <-$ D1'; ...; rm' <-$ Dm'; (vs1) <- A1(b1); ...; (vsk) <- Ak(bk);!

   Given a judgment 'G : ev', renaming 'ren' (bij. mapping from variables
   ri, vsi_j to variables), we rename the assumption using 'ren' and check
   that the first n lines of 'G' conincide with the samplings from the
   resulting assumption.

   The remainder of 'G' must have the following form:
   \begin{verbatim}
   ---
   let a1 = e1;
   C1;                          |
   let vs1_1 =  a1_1;           \  := D1
   ...;                         /  
   let vs1_|vs1| =  a1_|vs1|;   |

   ...

   let ak = ek;
   Ck;                          |
   let vsk_1 = ak_1;            \  := Dk
   ...;                         /
   let vsk_|vsk| = ak_|vsk|;    |
   --
   
   where for all i in [k],
     vars(Di\sigma_i) \cap {r1,..,rn} = emptyset.

  \end{verbatim}
  To obtain the new game, we just replace the prefix and replace
     ei by bi.

  To obtain such a game, it is important that for all i, it holds that
    $vars(e_i) \subseteq \{r1,..,rn\} \cup vs_{earlier}$.
  To achieve this, we must perform let_abstract for args last, front to
  back, and ensure that we do not use other variables.

  [*] Some extensions like allowing let-bindings in assumptions might be
      very simple while allowing samplings in between the adversary calls
      might be more complicated. This would allow for adaptive sampling,
      i.e., using vsj in the excepted expressions.
i*)

type assm_dec = {
  ad_name       : string;       (*r name of assumption *)
  ad_inf        : bool;         (*r information-theoretic assumption *)
  ad_prefix1    : gdef;         (*r prefix for left *)
  ad_prefix2    : gdef;         (*r prefix for right *)
  ad_acalls     : (Asym.t * Vsym.t list * (expr * expr)) list;
                                (*r adversary calls (same asym and
                                    returned variables and argument
                                    expression on left and right *)
  ad_symvars    : vs list list; (*r symmetric in given variables *)
}

let pp_acall_dec fmt (asym,vs1,(args1,args2)) =
  F.fprintf fmt "(%a) <- %a(%a | %a)@\n"
    (pp_list "," Vsym.pp) vs1 Asym.pp asym pp_exp args1 pp_exp args2

let pp_assm_dec fmt ad =
  F.fprintf fmt "assumption %s:@\n" ad.ad_name;
  F.fprintf fmt "prefix left:@\n%a@\n"  (pp_gdef ~nonum:false) ad.ad_prefix1;
  F.fprintf fmt "prefix right:@\n%a@\n" (pp_gdef ~nonum:false) ad.ad_prefix2;
  F.fprintf fmt "adversary calls:@\n%a@\n" (pp_list "@\n" pp_acall_dec) ad.ad_acalls;
  F.fprintf fmt "symvars: %a@\n" (pp_list "; " (pp_list "," Vsym.pp)) ad.ad_symvars

let mk_assm_dec name inf gd1 gd2 symvars =
  ignore (Wf.wf_gdef Wf.NoCheckDivZero gd1);
  ignore (Wf.wf_gdef Wf.NoCheckDivZero gd2);
  let (pref1,suff1) = L.partition (function GCall _ -> false | _ -> true) gd1 in
  let (pref2,suff2) = L.partition (function GCall _ -> false | _ -> true) gd2 in
  let rec go acc acalls1 acalls2 =
    match acalls1, acalls2 with
    | [], [] ->
      L.rev acc
    | GCall(vres1,asym1,arg1,od1)::acalls1, GCall(vres2,asym2,arg2,od2)::acalls2 ->
      if not (Asym.equal asym1 asym2) then
        tacerror
          "adversary calls in decisional assumption must match up: %a vs %a"
          Asym.pp asym1 Asym.pp asym2;
      if not (od1 = [] && od2 = []) then
        tacerror "decisional assumption with oracles not supported";
      if not (list_equal Vsym.equal vres1 vres2) then
        tacerror "decisional assumption return variables must match up: %a vs %a"
          (pp_list "," Vsym.pp) vres1 (pp_list "," Vsym.pp) vres2;
      go ((asym1,vres1,(arg1,arg2))::acc) acalls1 acalls2
    | _, _ ->
      tacerror "invalid decisional assumption"
  in
  let assm = {
    ad_name    = name;
    ad_inf     = inf;
    ad_prefix1 = pref1;
    ad_prefix2 = pref2;
    ad_acalls  = go [] suff1 suff2;
    ad_symvars = symvars }
  in
  assm
  
let needed_vars_dec dir assm =
  let toSym se =
    Se.fold (fun e s -> Vsym.S.add (destr_V e) s) se Vsym.S.empty
  in
  let w1 = toSym(write_gcmds assm.ad_prefix1) in
  let w2 = toSym(write_gcmds assm.ad_prefix2) in
  let diff = if dir = LeftToRight then Vsym.S.diff w2 w1 else Vsym.S.diff w1 w2 in
  Vsym.S.elements diff

let private_vars_dec assm =
  L.fold_left
    (fun vset cmd ->
      match cmd with GSamp(v,_) -> Se.add (mk_V v) vset | _ -> assert false)
    Se.empty
    (assm.ad_prefix1@assm.ad_prefix2)
    
let inst_dec ren assm =
  let ren_v vs = try Vsym.M.find vs ren with Not_found -> vs in
  let ren_acall (asym,vres,(e1,e2)) =
    (asym,L.map ren_v vres,(Game.subst_v_e ren_v e1,Game.subst_v_e ren_v e2))
  in
  let subst_g = Game.subst_v_gdef ren_v in
  { ad_name     = assm.ad_name;
    ad_inf      = assm.ad_inf;
    ad_prefix1  = subst_g assm.ad_prefix1;
    ad_prefix2  = subst_g assm.ad_prefix2;
    ad_acalls   = L.map ren_acall assm.ad_acalls; 
    ad_symvars  = L.map (L.map ren_v) assm.ad_symvars;
  }

(*i ----------------------------------------------------------------------- i*)
(* \hd{Computational assumptions} *)

type assm_type = A_Succ | A_Adv

let pp_atype fmt = function
  | A_Succ -> pp_string fmt "Succ"
  | A_Adv  -> pp_string fmt "Adv"

type assm_comp = {
  ac_name       : string;       (*r name of assumption *)
  ac_inf        : bool;         (*r information-theoretic assumption *)
  ac_type       : assm_type;
  ac_prefix     : gdef;         (*r prefix of assumption *)
  ac_event      : Expr.expr;    (*r event expression *)
  ac_acalls     : (Asym.t * Vsym.t list * expr) list;
   (*r adversary calls: asym, returned variables, and argument *)
  ac_symvars    : vs list list; (*r symmetric in given variables *)
}

let pp_acall_comp fmt (asym,vs1,args1) =
  F.fprintf fmt "(%a) <- %a(%a)@\n"
    (pp_list "," Vsym.pp) vs1 Asym.pp asym pp_exp args1

let pp_assm_comp fmt ac =
  F.fprintf fmt "assumption %s (%a):@\n" ac.ac_name pp_atype ac.ac_type;
  F.fprintf fmt "prefix left:@\n%a@\n"  (pp_gdef ~nonum:false) ac.ac_prefix;
  F.fprintf fmt "adversary calls:@\n%a@\n" (pp_list "@\n" pp_acall_comp) ac.ac_acalls;
  F.fprintf fmt "symvars: %a@\n" (pp_list "; " (pp_list "," Vsym.pp)) ac.ac_symvars

let mk_assm_comp name inf atype gd ev sym_vars =
  ignore (Wf.wf_se Wf.NoCheckDivZero { se_gdef = gd; se_ev = ev});
  let (pref,suff) = L.partition (function GCall _ -> false | _ -> true) gd in
  let rec go acc acalls =
    match acalls with
    | [] ->
      L.rev acc
    | GCall(vres,asym,arg,od)::acalls ->
      if not (od = []) then
        tacerror "computational assumption with oracles not supported yet";
      go ((asym,vres,arg)::acc) acalls
    | _ ->
      tacerror "invalid computational assumption"
  in
  let ac = {
    ac_name       = name;
    ac_inf        = inf;
    ac_type       = atype;
    ac_prefix     = pref;
    ac_event      = ev;
    ac_acalls     = go [] suff;
    ac_symvars    = sym_vars;
  }
  in
  log_t (lazy (fsprintf "comp. assm. defined:@\n@[<hov 4>  %a@]" pp_assm_comp ac));
  ac

let private_vars_comp assm =
  L.fold_left
    (fun vset cmd ->
      match cmd with GSamp(v,_) -> Se.add (mk_V v) vset | _ -> assert false)
    Se.empty
    assm.ac_prefix

let inst_comp ren assm =
  let ren_v (x:Vsym.t) = try Vsym.M.find x ren with Not_found -> x in
  let ren_acall (asym,vres,e) = (asym, L.map ren_v vres, subst_v_e ren_v e) in
  let subst_g = Game.subst_v_gdef ren_v in
  { assm with
    ac_prefix     = subst_g assm.ac_prefix;
    ac_event      = subst_v_e ren_v assm.ac_event;
    ac_acalls     = L.map ren_acall assm.ac_acalls;
    ac_symvars    = L.map (L.map ren_v) assm.ac_symvars;
  }

