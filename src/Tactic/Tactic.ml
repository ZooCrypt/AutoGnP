(*s Tactic engine: transformations of theory and proof states. *)

(*i*)
open Abbrevs
open Expr
open ExprUtils
open Type
open Util
open Nondet
open Syms
open TheoryTypes
open TheoryState
open Rules
open CoreTypes
open RewriteRules
open AssumptionRules
open RandomRules
open RindepRules
open CrushRules
open CaseRules
open Game

module Ht = Hashtbl
module PT = ParserTypes
module PU = ParserUtil
module CR = CoreRules

let log_i ls = mk_logger "Norm" Bolt.Level.INFO "NormField" ls
(*i*)


(*i ----------------------------------------------------------------------- i*)
(* \hd{Utility functions} *)

(* compute diff between the two given proof-trees *)
let diff_step ops nps =
  match ops with
  | Some ops ->
    let get_pt ps =
      CR.get_proof (prove_by_admit "" ps) |> simplify_proof_tree
    in
    fsprintf "@\n  @[%a@]"
      (pp_list "@\n" (pp_proof_tree pp_unit ~hide_admit:true false))
      (diff_proof_tree (get_pt ops,get_pt nps))
  | None -> ""

(* pretty-print judgment *)
let pp_jus i fmt jus =
  match jus with
  | [] -> F.printf "No remaining goals, proof completed.@\n"
  | jus ->
    let n = L.length jus in
    let goal_num = if n = 1 then "" else F.sprintf " (of %i)" n in
    let pp_goal i ju =
      F.fprintf fmt "goal %i%s: %a@\n@\n" (i + 1) goal_num pp_ju ju
    in
    L.iteri pp_goal (Util.take i jus)


let gpos_of_offset ju i =
  if i < 0 then L.length ju.ju_se.se_gdef + i + 1 else i

let epos_of_offset ju i =
  let ev = ju.ju_se.se_ev.ev_expr in
  if i < 0 && is_Land ev
  then L.length (destr_Land ev) + i + 1
  else i

let find_gvar ju s = 
  let test = function
    | GLet(vs,_) | GSamp(vs,_) -> s = Id.name vs.Vsym.id 
    | GAssert _ -> false
    | GCall(vss,_,_,_) -> L.exists (fun vs -> s = Id.name vs.Vsym.id) vss
  in
  try find_at test ju.ju_se.se_gdef
  with Not_found -> tacerror "variable not found in game %s" s

let gpos_of_apos ju ap =
  match ap with
  | PT.AbsPos i -> i
  | PT.Var s    -> find_gvar ju s
  | PT.Pos i when i >= 0 -> (gpos_of_offset ju i) - 1
  | PT.Pos i -> (gpos_of_offset ju i)

let interval ju (i1,i2) = 
  let i1 = opt (gpos_of_apos ju) 0 i1 in
  let i2 = 
    opt_f (gpos_of_apos ju) (fun _ -> L.length ju.ju_se.se_gdef - 1) i2
  in
  i1, i2

let t_swap inter delta ju = 
  let (i1,i2) = interval ju inter in
  if i2 < i1 then tacerror "swap: empty interval [%i .. %i]" i1 i2;
  let delta = 
    match delta with
    | PT.Pos i -> i
    | PT.Var s -> 
      let p = find_gvar ju s in
      if p <= i1 then p - i1
      else if p >= i2 then p - i2
      else tacerror "swap: invalid position %s" s
    | PT.AbsPos p ->
      if p <= i1 then p - i1
      else if p >= i2 then p - i2
      else tacerror "swap: invalid position %i" p
  in  
  let li = list_from_to i1 (i2+1) in
  let lt = L.map (fun i -> CR.t_swap i delta) li in
  if delta < 0 then Rules.t_seq_fold lt ju
  else Rules.t_seq_fold (L.rev lt) ju

let ranges ju l = 
  let l = L.map (interval ju) l in
  if l = [] then None else Some l

(*i ----------------------------------------------------------------------- i*)
(* \hd{Tactic handling} *)
exception Handle_this_tactic_instead of PT.tactic
            
let rec handle_tactic ts tac =
  let input_ts = ts in try (
  let ps = get_proof_state ts in
  let ju = match ps.CR.subgoals with
    | ju::_ -> ju
    | []    -> tacerror "cannot apply tactic: there is no goal"
  in
  let apply ?adecls r =
    try
      let ts = opt (fun ad -> { ts with ts_adecls = ad }) ts adecls in
      let pss = CR.apply_first r ps in
      begin match pull pss with
      | Left None     -> tacerror "tactic failed, no error message"
      | Left (Some s) -> tacerror "%s" (Lazy.force s)
      | Right(nps,pss) ->
        let ops = Some ps in
        let ts' = { ts with ts_ps = ActiveProof(nps,[],pss,ops) } in
        (ts', lazy (diff_step ops nps))
      end
    with
    | Wf.Wf_div_zero es ->
      tacerror "Wf: Cannot prove that %a nonzero" (pp_list "," pp_exp) es
    | Wf.Wf_var_undef(v,e,def_vars) ->
      tacerror "Wf: Var %a undefined in %a, not in %a"
        Vsym.pp v pp_exp e
        (pp_list "," Vsym.pp) (Vsym.S.elements def_vars)
  in
  let rec interp_tac tac ju =
    let vmap_g = vmap_of_globals ju.ju_se.se_gdef in
    let e_pos = epos_of_offset ju in
    let get_pos = gpos_of_apos ju in
    
    let parse_e se = PU.expr_of_parse_expr vmap_g ts Unqual se in
   
    let parse_ev se = 
      let vmap_se = vmap_of_se ju.ju_se in
      PU.expr_of_parse_expr vmap_se ts Unqual se in

    let mk_new_var sv ty = assert (not (Ht.mem vmap_g (Unqual,sv))); Vsym.mk sv ty in
    match tac with
    | PT.Rnorm                 -> t_norm ~fail_eq:false ju
    | PT.Rnorm_nounfold        -> t_norm_nounfold ju
    | PT.Rlet_unfold([])       -> t_unfold_only ju
    | PT.Rlet_unfold(l)        -> 
      let l = L.rev l in
      let lt = L.map (fun i ju -> t_let_unfold (gpos_of_apos ju i) ju) l in
      Rules.t_seq_fold lt ju
  
    | PT.Rswap(i,j)            -> t_swap i j ju
    | PT.Rdist_eq              -> Rules.t_dist_eq ju
    | PT.Rdist_sym             -> CR.t_dist_sym ju
    | PT.Rremove_ev(is)        -> CR.t_remove_ev is ju
    | PT.Rsplit_ev(i)          -> CR.t_split_ev (e_pos i) ju
    | PT.Rsplit_ineq(i)        -> SimpRules.t_split_ineq (e_pos i) ju
    | PT.Rrewrite_ev(i,d)      -> CR.t_rw_ev (e_pos i) d ju
    | PT.Rcrush(finish,mi)     -> t_crush finish mi ts ps ju
  
      (* FIXME: all tactics interpreted wrt. the same theory state,
                OK for tactics that do not change the theory state. *)
    | PT.Rseq tacs ->
      t_seq_fold (L.map interp_tac tacs) ju

    | PT.Rcase_ev(Some(se)) ->
      CR.t_case_ev (parse_ev se) ju
  
    | PT.Rsubst(i,e1,e2,mupto) ->
      t_subst (Util.opt get_pos 0 i) (parse_e e1) (parse_e e2) (map_opt get_pos mupto) ju
  
    | PT.Rrename(v1,v2) ->
      let v1 = Ht.find vmap_g (Unqual,v1) in
      let v2 = mk_new_var v2 v1.Vsym.ty in
      t_rename v1 v2 ju
  
    | PT.Rcase_ev(None) ->
      t_case_ev_maybe ju
  
    | PT.Rexcept(Some(i),Some(ses)) ->
      CR.t_except (get_pos i) (L.map (parse_e) ses) ju
  
    | PT.Rexcept(i,ses) ->
      t_rexcept_maybe (map_opt get_pos i) ses ju
  
    | PT.Rswap_oracle(op,j)    -> CR.t_swap_oracle op j ju
    | PT.Rrewrite_orcl(op,dir) -> CR.t_rewrite_oracle op dir ju
  
    | PT.Rfalse_ev             -> CR.t_false_ev ju
    | PT.Rindep(exact)         -> t_random_indep ts exact ju
  
    | PT.Rnorm_unknown(is) ->
      let vs = L.map (fun s -> mk_V (Ht.find vmap_g (Unqual,s))) is in
      t_norm_unknown ts vs ju
  
    | PT.Rlet_abstract(Some(i),sv,Some(se),mupto,no_norm) ->
      let e = parse_e se in
      let v = mk_new_var sv e.e_ty in
      t_let_abstract (get_pos i) v e (map_opt get_pos mupto) (not no_norm) ju

    | PT.Rlet_abstract(None,sv,Some(se),mupto,no_norm) ->
       raise (Handle_this_tactic_instead(PT.Rlet_abstract(Some (PT.Pos(-1)),sv,Some se, mupto, no_norm)))
                     
    | PT.Rlet_abstract_oracle(opos,sv,se,len,no_norm) ->
       let qual = Qual (PU.get_oname_from_opos ju.ju_se opos) in
       let vmap_o = vmap_in_orcl ju.ju_se opos in
       let e = PU.expr_of_parse_expr vmap_o ts qual se in
       let v = PU.create_var vmap_o ts qual sv e.e_ty in
       (*let v = mk_new_var sv e.e_ty in*)
       t_let_abstract_oracle opos v e len (not no_norm) ju

    | PT.Rlet_abstract_deduce(keep_going,i,sv,se,mupto) ->
      let e = parse_e se in
      let v = mk_new_var sv e.e_ty in
      t_abstract_deduce ~keep_going ts (get_pos i) v e (map_opt get_pos mupto) ju
      
    | PT.Rassert(i,Some se) ->
      let e = parse_e se in
      CR.t_assert (get_pos i) e ju

    | PT.Rassert(i,None) ->
      let t_remove_assert ju =
        let se = ju.ju_se in
        match get_se_ctxt se (get_pos i) with
        | GAssert(e), sec ->
          let se_new = set_se_ctxt [] sec in
          (CR.t_trans se_new
           @>> [ CR.t_dist_sym @> CR.t_assert (get_pos i) e
                 @>> [ CR.t_id; Rules.t_dist_eq]
               ; CR.t_id ]) ju
        | _ ->
          tacerror "no assert at given position %i" (get_pos i)
      in
      t_remove_assert ju

    | PT.Rswap_to_main(i_j_k,vs)  -> CR.t_swap_main i_j_k vs ju

    | PT.Rswap_to_orcl(p,(i,j,k),sv) ->
      let ci = get_pos p in
      if (ci + 1<>i) then
        tacerror "swap_to_main: variable in main must directly precede oracle";
      if (k<>0) then
        tacerror "swap_to_main: can only swap variable to start of oracle";
      let t_swap_to_orcl ju =
        log_i (lazy (fsprintf "i=%i j=%i k=%i" i j k));
        let se = ju.ju_se in
        assert (ci < i);
        let op = (i,j,k,Ohyb OHeq) in
        let _, seoc =  get_se_octxt_len se op 0 in
        let oname = Id.name seoc.seoc_osym.Osym.id in
        match split_n ci (L.rev seoc.seoc_sec.sec_left) with
        | cleft, GSamp(vsm,d), cright ->
          log_i (lazy (fsprintf "cleft=%a cright=%a"
                         (pp_gdef ~nonum:false) cleft (pp_gdef ~nonum:false) cright));
          let vmap = Hashtbl.create 17 in
          let vso = PU.create_var vmap ts (Qual oname) sv vsm.Vsym.ty in
          let subst e = e_replace (mk_V vsm) (mk_V vso) e in
          let seoc =
            { seoc with
              seoc_return = subst seoc.seoc_return;
              seoc_sec =
                { sec_left = L.rev (L.rev_append cleft cright);
                  sec_right = L.map (map_gcmd_exp subst) seoc.seoc_sec.sec_right;
                  sec_ev = map_ev_exp subst seoc.seoc_sec.sec_ev; } }
          in
          let lcright = L.map (map_lcmd_exp subst) seoc.seoc_cright in
          let se = set_se_octxt [LSamp(vso,d)] { seoc with seoc_cright = lcright } in
          (CR.t_trans se @>> [ CR.t_dist_sym
                               @> CR.t_swap_main (i-1,j,k) "rr" @> t_dist_eq
                             ; CR.t_id]) ju
        | _ -> tacerror "cannot swap sampling to oracle, given position not a sampling"
      in
      t_swap_to_orcl ju
  
    | PT.Rlet_abstract(None,sv,None,mupto,no_norm) ->
      let v = mk_new_var sv ju.ju_se.se_ev.ev_expr.e_ty in
      let max = L.length ju.ju_se.se_gdef in
      t_let_abstract max v ju.ju_se.se_ev.ev_expr (map_opt get_pos mupto) (not no_norm) ju
  
    | PT.Rlet_abstract(_,_,_,_,_) ->
      tacerror "No placeholders or placeholders for both position and event"
  
    | PT.Rconv(Some sgd,sev) ->
      let vmap2 = Hashtbl.create 134 in
      let gd2 = PU.gdef_of_parse_gdef vmap2 ts sgd in
      let ev2 = PU.ev_of_parse_ev vmap2 ts sev in
      CR.t_conv true { se_gdef = gd2; se_ev = ev2 } ju

    | PT.Rconv(None,sev) ->
      let ev2 = PU.ev_of_parse_ev vmap_g ts sev in
      CR.t_conv true { se_gdef = ju.ju_se.se_gdef; se_ev = ev2 } ju
  
    | PT.Rtrans(sgd,sev) ->
      let vmap2 = Hashtbl.create 134 in
      let gd2 = PU.gdef_of_parse_gdef vmap2 ts sgd in
      let ev2 = PU.ev_of_parse_ev vmap2 ts sev in
      CR.t_trans { se_gdef = gd2; se_ev = ev2 } ju

    | PT.Rtrans_diff(dcmds) ->
      let vmap = Hashtbl.copy vmap_g in
      let rec app_diff dcmds ju =
        let get_pos = gpos_of_apos ju in
        let se = ju.ju_se in        
        match dcmds with
        | [] -> ju.ju_se
        | PT.Drename(v1,v2,mupto)::dcmds ->
          let v1 = Ht.find vmap (Unqual,v1) in
          let v2 = mk_new_var v2 v1.Vsym.ty in
          let maxlen = L.length se.se_gdef in
          let mupto = map_opt (fun p -> succ (get_pos p)) mupto in
          let rn_len = from_opt maxlen mupto in
          let a_cmds, sec = get_se_ctxt_len se ~pos:0 ~len:rn_len in
          let sigma v = if Vsym.equal v v1 then v2 else v in
          let a_cmds = subst_v_gdef sigma a_cmds in
          let ev = if mupto=None then subst_v_ev sigma sec.sec_ev else sec.sec_ev in
          app_diff dcmds { ju with ju_se = (set_se_ctxt a_cmds { sec with sec_ev = ev }) }
        | PT.Dsubst(p,e1,e2)::dcmds ->
          let p = get_pos p in
          let e1 = PU.expr_of_parse_expr vmap ts Unqual e1 in
          let e2 = PU.expr_of_parse_expr vmap ts Unqual e2 in
          let subst a = e_replace e1 e2 a in
          let l,r = cut_n p se.se_gdef in
          let new_se = 
            { se_gdef = L.rev_append l (map_gdef_exp subst r); 
              se_ev   = map_ev_exp subst se.se_ev }
          in
          app_diff dcmds { ju with ju_se = new_se }
        | PT.Dinsert(p,gcmds)::dcmds ->
          let i = get_pos p in
          let _, sec = get_se_ctxt_len se ~pos:i ~len:0 in
          let gcmds = PU.gdef_of_parse_gdef vmap ts gcmds in
          app_diff dcmds { ju with ju_se = (set_se_ctxt gcmds sec) }
      in
      let t_diff ju =
        CR.t_trans (app_diff dcmds ju) ju
      in
      t_diff ju
  
    | PT.Rassm_dec(exact,maname,mdir,mrngs,msvs) ->
      t_assm_dec ts exact maname mdir (ranges ju mrngs) msvs ju
  
    | PT.Rnorm_solve(se) ->
      let e = parse_e se in
      RewriteRules.t_norm_solve e ju
  
    | PT.Rexcept_orcl(op,pes) ->
      let vmap = vmap_in_orcl ju.ju_se op in
      let es = L.map (PU.expr_of_parse_expr vmap ts Unqual) pes in
      CR.t_except_oracle op es ju
  
    | PT.Rctxt_ev (mj,Some(sv,_mt,e)) ->
      let j = match mj with
        | Some j -> j
        | None -> tacerror "position placeholder not allowed if context is given"
      in
      let ev = ju.ju_se.se_ev.ev_expr in
      let b =
        match ev.e_node with
        | Nary(Land,es) when j < L.length es ->
          L.nth es j
        | _ when j = 0 -> ev
        | _ -> tacerror "rctxt_ev: bad index"
      in
      let ty =
        if is_Eq b then (fst (destr_Eq b)).e_ty
        (* else if is_Exists b then
          let (e1,_,_) = destr_Exists b in e1.e_ty *)
        else tacerror "rctxt_ev: bad event"
      in
      let vmap = vmap_of_globals ju.ju_se.se_gdef in
      let v1 = PU.create_var vmap ts Unqual sv ty in
      let e1 = PU.expr_of_parse_expr vmap ts Unqual e in
      let c = v1, e1 in
      CR.t_ctxt_ev j c ju
                   
    | PT.Runwrap_quant_ev j ->
      let r_unwrap_quant_ev ju =
        let ev = ju.ju_se.se_ev in
        let main_binding = ev.ev_binding and ev_exprs = ev.ev_expr in
        let l,q_expr,r = match ev_exprs.e_node with
          | Nary(Land,es) when j < L.length es -> Util.split_n j es
          | _ when j = 0 -> [],ev_exprs,[]
          | _ -> tacerror "unwrap_quant_ev: bad index %i" j
        in
        let (q,b,e) =
          try destr_Quant q_expr
          with
            Destr_failure _ -> tacerror "unwrap_quant_ev : no quantification in event %a" pp_exp q_expr
        in
        if q = All then tacerror "forall quantification not handled yet.";
        let new_ev = { ev with ev_binding = b :: main_binding; ev_expr = mk_Land (List.rev_append l (e :: r))} in
        let new_se = {ju.ju_se with se_ev = new_ev} in
        let new_ju = {ju with ju_se = new_se} in
        Runwrap_quant_ev j,[new_ju]
      in
      CR.prove_by(r_unwrap_quant_ev) ju

    | PT.Rinjective_ctxt_ev (j,Some (svx,None,ey),Some (svy,None,ex)) ->
      let ev_expr = ju.ju_se.se_ev.ev_expr in
      let b = match ev_expr.e_node with
        | Nary(Land,es) when j < L.length es -> L.nth es j
        | _ when j = 0 -> ev_expr
        | _ -> tacerror "injective_ctxt_ev: bad index %i" j
      in
      let tyx =
        if is_Eq b then (* (fst (destr_Eq b)).e_ty *)
          raise (Handle_this_tactic_instead (PT.Rctxt_ev (Some j,Some(svx,None,ey))))
        else if is_InEq b then (fst (destr_Eq (destr_Not b))).e_ty
        else tacerror "injective_ctxt_ev: bad event %a, expected '=' or '<>'" pp_exp b
      in
      let vmap = vmap_of_globals ju.ju_se.se_gdef in
      (* Adding quantified variables *)
      List.iter
        (fun (vs,o) -> List.iter
          (fun v -> ignore(PU.create_var vmap ts Unqual (Id.name v.Vsym.id) (Oracle.get_dom o))) vs)
        ju.ju_se.se_ev.ev_binding;
      let vx = PU.create_var vmap ts Unqual svx tyx in
      let ey = PU.expr_of_parse_expr vmap ts Unqual ey in 
      let vy = PU.create_var vmap ts Unqual svy ey.e_ty in
      let ex = PU.expr_of_parse_expr vmap ts Unqual ex in
      let c1 = vx, ey and c2 = vy, ex in
      CR.t_injective_ctxt_ev j c1 c2 ju

    | PT.Rinjective_ctxt_ev _ -> assert false
  
    | PT.Rctxt_ev (mj,None) ->
      SimpRules.t_ctx_ev_maybe mj ju
  
    | PT.Rsimp must_finish ->
      SimpRules.t_simp must_finish 20 ju
  
    | PT.Rassm_comp(exact,maname,mrngs) ->
      t_assm_comp ts exact maname (ranges ju mrngs) ju
  
    | PT.Rrnd(exact,mi,mctxt1,mctxt2,mgen) ->
      let mgen = map_opt parse_e mgen in
      t_rnd_maybe ts exact (map_opt get_pos mi) mctxt1 mctxt2 mgen ju

    | PT.Rrnd_exp(exact,ids) ->
      let to_tac (i,mi2) =
        let v = Ht.find vmap_g (Unqual,i) in
        let ename =
          let li = String.lowercase i in
          from_opt (if li<>i then li else "e_"^i) mi2
        in
        let gname = destr_G v.Vsym.ty in
        let e = PT.Exp(PT.CGen (Groupvar.name gname), PT.V(Unqual,ename)) in
        PT.Rrnd(exact,Some (PT.Var i), Some (ename,Some PT.Fq,e),None,None)
      in
      t_seq_fold (L.map (fun i -> interp_tac (to_tac i)) ids) ju
  
    | PT.Rrnd_orcl(mopos,mctxt1,mctxt2) ->
      t_rnd_oracle_maybe ts mopos mctxt1 mctxt2 ju
  
    | PT.Rhybrid((i,j),(lcmds,eret)) ->
      let se = ju.ju_se in
      let opos = (i,j,0,Onohyb) in
      let vmap = vmap_in_orcl se opos in
      let _, seoc = get_se_octxt se opos in
      let oname = Id.name seoc.seoc_osym.Osym.id in
      let lcmds = L.map (PU.lcmd_of_parse_lcmd vmap ts ~oname) lcmds in
      let eret = PU.expr_of_parse_expr vmap ts (Qual oname) eret in
      CR.t_hybrid i j lcmds eret ju

    | PT.Radd_test(_) | PT.Deduce(_) | PT.FieldExprs(_) | PT.Rguard _ ->
      tacerror "add_test and debugging tactics cannot be combined with ';'"

    | PT.Rbad(1,Some ap,_vsx) ->
      let p = gpos_of_apos ju ap in
      let vsx = failwith "undefined" in
      CR.t_bad CaseDist p vsx ju
    | PT.Rbad(2,Some ap,_vsx) ->
      let p = gpos_of_apos ju ap in
      let vsx = failwith "undefined" in
      CR.t_bad UpToBad p vsx ju
    | PT.Rbad(i,None,vsx) ->
      raise (Handle_this_tactic_instead(PT.Rbad(i, Some (PT.Pos (-2)), vsx)))
    | PT.Rcheck_hash_args(opos) ->
      CR.t_check_hash_args opos ju
    | PT.Rbad _ | PT.RbadOracle _ ->
      tacerror "Wrong RBad tactic call in Tactic.ml";
    | PT.Rguess(aname, fvs) ->
      if (Mstring.mem aname ts.ts_adecls) then
        tacerror "rguess: adversary with same name already declared";
      let ev = ju.ju_se.se_ev in
      let vs = 
        match ev.ev_binding with
        | [vs,_] -> vs
        | _ ->  tacerror "rguess: invalid binding" in
      let asym = Asym.mk aname (mk_Prod []) (ty_prod_vs vs) in
      if not (L.length fvs = L.length vs) then
        tacerror "Error, 'guess' rule requires here %i variable(s), but got %i" (L.length vs) (L.length fvs);
      let vmap = vmap_of_globals ju.ju_se.se_gdef in
      let fvs = 
        L.map2 (fun v v' -> PU.create_var vmap ts Unqual v v'.Vsym.ty) 
          fvs vs in
      CR.t_guess asym fvs ju
                 
    | PT.Rfind((bd,body),arg,aname,fvs) ->
      if (Mstring.mem aname ts.ts_adecls) then
        tacerror "rguess: adversary with same name already declared";
      let ev = ju.ju_se.se_ev in
      let vs = 
        match ev.ev_binding with
        | [vs,_] -> vs
        | _ ->  tacerror "rfind: invalid binding" in
      let arg = parse_e arg in
      let asym = Asym.mk aname (arg.e_ty) (ty_prod_vs vs) in
      if not (L.length fvs = L.length vs) then
        tacerror "Error, 'find' rule requires here %i variable(s), but got %i" (L.length vs) (L.length fvs);
      let vmap = vmap_of_globals ju.ju_se.se_gdef in
      let fvs = 
        L.map2 (fun v v' -> PU.create_var vmap ts Unqual v v'.Vsym.ty) 
          fvs vs in
      (* typing of f *)
      let f = 
        let vmap_se = vmap_of_se ju.ju_se in
        let bd = 
          L.map2 (fun v e -> PU.create_var vmap_se ts Unqual v e.e_ty)
            bd (destr_Tuple_nofail arg) in
        let body =
          PU.expr_of_parse_expr vmap_se ts Unqual body in
        bd,body in
      
      CR.t_find f arg asym fvs ju
  in

 let vmap_g = vmap_of_globals ju.ju_se.se_gdef in
 match tac with     
 | PT.Radd_test(Some(opos),Some(t),Some(aname),Some(fvs)) ->
   (* create symbol for new adversary *)
   let se = ju.ju_se in
   let _, seoc = get_se_octxt se opos in
   let vmap = vmap_in_orcl se opos in
   let oasym = seoc.seoc_asym in
   let oname = Id.name seoc.seoc_osym.Osym.id in
   let t = PU.expr_of_parse_expr vmap ts (Qual oname) t in
   let oty = seoc.seoc_osym.Osym.dom in
   let destr_prod ty = match ty.ty_node with
     | Prod(tys) -> tys
     | _ -> [ty]
   in
   if (Mstring.mem aname ts.ts_adecls) then
     tacerror "radd_test: adversary with same name already declared";
   let asym = Asym.mk aname oasym.Asym.dom oty in
   let adecls = Mstring.add aname asym ts.ts_adecls in
   let tys = destr_prod oty in
   (* create variables for returned values *)
   if not (L.length fvs = L.length seoc.seoc_oargs) then
     tacerror "number of given variables does not match type";
   let fvs =
     match fvs with
     | [fv] -> [ PU.create_var vmap ts Unqual fv oty ]
     | _    -> L.map2 (fun v ty -> PU.create_var vmap ts Unqual v ty) fvs tys
   in
   apply ~adecls (CR.t_add_test opos t asym fvs)
  
 | PT.Radd_test(None,None,None,None) ->
   apply t_add_test_maybe
  
 | PT.Radd_test(_,_,_,_) ->
   tacerror "radd_test expects either all values or only placeholders"

 | PT.Deduce(ppt,pes,pe) ->
   let es = L.map (PU.expr_of_parse_expr vmap_g ts Unqual) pes in
   let e = PU.expr_of_parse_expr vmap_g ts Unqual pe in
   log_i (lazy (fsprintf "deduce %a |- %a@\n" (pp_list "," pp_exp) es pp_exp e));
   (try
      let frame =
        L.mapi
          (fun i e -> (e, I (mk_V (Vsym.mk ("x"^(string_of_int i)) e.e_ty))))
          es
      in
      let recipe = Deduc.invert ~ppt_inverter:ppt ts frame e in
      log_i (lazy (fsprintf "Found %a@\n" pp_exp recipe))
    with
      Not_found ->
        tacerror "Not found@\n");
   (ts,lazy "")

  
 | PT.FieldExprs(pes) ->
   let es = L.map (PU.expr_of_parse_expr vmap_g ts Unqual) pes in
   let ses = ref Se.empty in
     Game.iter_se_exp ~iexc:true
       (fun e' -> e_iter_ty_maximal mk_Fq
          (fun fe -> if L.exists (fun e -> e_exists (e_equal e) fe) es
                     then ses := Se.add fe !ses) e')
       ju.ju_se;
   let res = (lazy (fsprintf "field expressions with %a: @\n@[<hov 2>  %a@]"
                      (pp_list ", " pp_exp) es
                      (pp_list ",@\n" pp_exp) (Se.elements !ses)))
   in
   log_i res;
   (ts,res)

   (* remaining tactics that can be nested with seq *)
 | PT.Rguard(opos, t) ->
   (* create symbol for new adversary *)
   let se = ju.ju_se in
   let seoc = 
     if t = None then snd (get_se_octxt se opos)
     else snd (get_se_octxt_len se opos 0)
   in
   let vmap = vmap_in_orcl se opos in
   let oname = Id.name seoc.seoc_osym.Osym.id in
   let t = map_opt (PU.expr_of_parse_expr vmap ts (Qual oname)) t in
   apply (CR.t_guard opos t)

 | _ ->
    apply (interp_tac tac)              
                       ) with
        Handle_this_tactic_instead new_tac -> handle_tactic input_ts new_tac

(*i ----------------------------------------------------------------------- i*)
(* \hd{Instruction handling} *)

let handle_instr verbose ts instr =
  match instr with
  | PT.Help(PT.Rinjective_ctxt_ev _) ->
    let msg =
      "Rule that allows replacing the i-th event expression (of type 'e1 = e2' or 'e1 <> e2')"^
      "by f(e1) and f(e2) provided f is injective (f_i verifying 'f_i(f(x)) = x' is required to prove it)"^
      "Usage : \n> injective_ctxt_ev [index] (x -> f(x)) (y -> f_i(y))."
    in
    (ts, msg)
  | PT.Help(PT.Rbad(i,_,_)) ->
    let msg =
      fsprintf
        ("Rule that allows to \"replace\" a random oracle call by a random sampling,\n"^^
         "provided you can bound the probability the expression queried to the RO is not queried elsewhere.\n\n"^^
         "Usage : \n> bad%i assgn_pos var_name.\n"^^
         "(where assgn_pos is a line_number, the name of a let-bound variable, or a placeholder (last line))\n\n"^^
         "The (game) command located at line_number must be a let binding of a random oracle call.")
        i
    in
    (ts, msg)
  | PT.Help(PT.Rfind _) ->
    let msg =
      "Rule to 'get' existential variable(s) 'vars' from the event into the main game \n"^
      "thanks to an adversary 'A_name' who is given 'args'. \n\n"^
      "Usage :\n> find (xs* -> f(xs,vars)) args A_name vars* ."
    in
    (ts, msg)
  | PT.Help (PT.Runwrap_quant_ev _) ->
    let msg =
      "Rule to unwrap the quantification from the j-th event to the main event quantification.\n"^
      "If j is not provided, it is assumed to be 0.\n\n"^
      "Usage :\n> unwrap_quant_ev [j]."
    in
    (ts, msg)
  | PT.Help (PT.Rcheck_hash_args _) ->
    let msg =
      "Rule to deduce from a guarded expression of the form\n'Exists h in L_H : h = e',\n"^
      "that any future hash call querying e is actually a lookup, i.e.,\n'H(e)' becomes 'm_H(e)'.\n\n"^
      "Usage :\n> check_hash_args (i,j,k)."
    in
    (ts, msg)
  | PT.Help _ -> assert false
  | PT.PermDecl(s,t) -> let s_inv = s ^ "_inv" in
     if Mstring.mem s_inv ts.ts_permdecls then
       tacerror "Permutation with the same name '%s' already declared." s;
     let f = Psym.mk s (PU.ty_of_parse_ty ts t) (create_permvar ts s) in
     let ts = { ts with ts_permdecls = Mstring.add s_inv f ts.ts_permdecls } in
     (ts, fsprintf "Declared permutation %s : " s)
  | PT.RODecl(s,ro,t1,t2) ->
    let oname = if ro then "random oracle" else "operator" in
    if Mstring.mem s ts.ts_rodecls then
      tacerror "%s with same name already declared." oname;
    let dom,codom=(PU.ty_of_parse_ty ts t1),(PU.ty_of_parse_ty ts t2) in
    let hs = Hsym.mk s ~ro dom codom in
    let ts_rodecls = Mstring.add s hs ts.ts_rodecls in
    let ts_lkupdecls =
      if ro then
        Mstring.add s (Hsym.mk s ~ro:true ~lkup:true dom codom) ts.ts_lkupdecls
                    else ts.ts_lkupdecls in
    let ts = { ts with ts_rodecls; ts_lkupdecls} in
    (ts, fsprintf "Declared %s" oname)

  | PT.EMDecl(s,g1,g2,g3) ->
    if Mstring.mem s ts.ts_emdecls then
      tacerror "Bilinear map with same name already declared.";
    let es = Esym.mk s (create_groupvar ts g1) (create_groupvar ts g2) (create_groupvar ts g3) in
    let ts = { ts with ts_emdecls = Mstring.add s es ts.ts_emdecls } in
    (ts, "Declared bilinear map.")

  | PT.ODecl(s,t1,t2) ->
    if Mstring.mem s ts.ts_odecls then
      tacerror "Oracle with same name already declared.";
    let os = Osym.mk s (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2) in
    let ts = { ts with ts_odecls = Mstring.add s os ts.ts_odecls } in
    (ts, Util.fsprintf "Declared oracle: %a" Osym.pp_long os)

  | PT.ADecl(s,t1,t2) ->
    if Mstring.mem s ts.ts_adecls then
      tacerror "adversary with same name already declared.";
    let asym = Asym.mk s (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2) in
    let ts = { ts with ts_adecls = Mstring.add s asym ts.ts_adecls } in
    (ts, Util.fsprintf "Declared adversary: %a" Asym.pp_long asym)

  | PT.AssmDec(s,inf,g0,g1,symvs) ->
    let vmap1 = Ht.create 137 in
    let vmap2 = Ht.create 137 in
    let g0 = PU.gdef_of_parse_gdef vmap1 ts g0 in
    let g1 = PU.gdef_of_parse_gdef vmap2 ts g1 in
    let vmap, sigma = merge_vmap vmap1 vmap2 in
    let g1 = subst_v_gdef sigma g1 in
    let parse_var s =
      try  Ht.find vmap (Unqual,s)
      with Not_found -> tacerror "unknown variable %s" s
    in
    let symvs = L.map (L.map parse_var) symvs in
    if Mstring.mem s ts.ts_assms_dec then
      tacerror "assumption with the same name already exists";
    let ts = {
      ts with
        ts_assms_dec =
        Mstring.add s (Assumption.mk_assm_dec s inf g0 g1 symvs) ts.ts_assms_dec
    }
    in
    (ts, "Declared decisional assumption.")

  | PT.AssmComp(s,inf,at,g,ev,symvs) ->
    let vmap = Ht.create 137 in
    let g = PU.gdef_of_parse_gdef vmap ts g in
    let parse_var s =
      try  Ht.find vmap (Unqual,s)
      with Not_found -> tacerror "unknown variable %s" s
    in
    let symvs = L.map (L.map parse_var) symvs in
    let ev = PU.ev_of_parse_ev vmap ts ev in
    let assm = Assumption.mk_assm_comp s inf at g ev symvs in
    if Mstring.mem s ts.ts_assms_comp then
      tacerror "assumption with the same name already exists";
    let ts = { ts with ts_assms_comp = Mstring.add s assm ts.ts_assms_comp } in
    (ts, "Declared computational assumption.")

  | PT.JudgAdv(gd,e) | PT.JudgSucc(gd,e)->
    let vmap = Ht.create 137 in
    let se = PU.se_of_parse_se vmap ts gd e in
    let pt = match instr with PT.JudgAdv _ -> Pr_Adv | _ -> Pr_Succ in
    let ju = { ju_se = se; ju_pr = pt } in
    let ps = first (CR.t_id ju) in
    ({ ts with ts_ps = ActiveProof(ps,[],mempty,None) }
    , "Started proof of judgment.")

  | PT.JudgDist(gd1,e1,gd2,e2) ->
    let vmap1 = Ht.create 137 in
    let se1 = PU.se_of_parse_se vmap1 ts gd1 e1 in
    let vmap2 = Ht.create 137 in
    let se2 = PU.se_of_parse_se vmap2 ts gd2 e2 in
    let ju = { ju_se = se1; ju_pr = Pr_Dist se2 } in
    let ps = first (CR.t_id ju) in
    ({ ts with ts_ps = ActiveProof(ps,[],mempty,None) }
    , "Started proof of judgment.")

  | PT.Apply(tac) ->
    let (ts,s) = handle_tactic ts tac in
    (ts, "Applied tactic"^(if verbose then ": "^Lazy.force s else "."))

  | PT.Back ->
    begin match ts.ts_ps with
    | ActiveProof(_,uback,back,ops) ->
      begin match pull back with
      | Left _ -> tacerror "Cannot backtrack"
      | Right(ps',pss) ->
        let ts' =
          { ts with ts_ps = ActiveProof(ps',(get_proof_state ts)::uback,pss,ops) }
        in
        (ts', "Backtracked to next alternative:"^diff_step ops ps')
      end
    | _ -> tacerror "last: no goals"
    end

  | PT.UndoBack(false) ->
    begin match ts.ts_ps with
    | ActiveProof(_,uback,back,ops) ->
      begin match uback with
      | [] -> tacerror "Cannot undo backtrack"
      | ps'::pss ->
        ({ ts with
           ts_ps = ActiveProof(ps',pss,mplus (ret (get_proof_state ts)) back,ops) }
        , "Backtracked to previous alternative:"^diff_step ops ps')
      end
    | _ -> tacerror "last: no goals"
    end

  | PT.UndoBack(true) ->
    begin match ts.ts_ps with
    | ActiveProof(_,uback,back,ops) ->
      begin match L.rev uback with
      | [] -> tacerror "Cannot undo backtrack"
      | ps'::pss ->
        let back' = mplus (mconcat pss) (mplus (ret (get_proof_state ts)) back) in
        ({ ts with
           ts_ps = ActiveProof(ps',[],back',ops) }
        , "Backtracked to first alternative:"^diff_step ops ps')
      end
    | _ -> tacerror "last: no goals"
    end

  | PT.Last ->
    begin match ts.ts_ps with
    | ActiveProof(ps,uback,back,ops) ->
      ({ ts with ts_ps = ActiveProof(CR.move_first_last ps,uback,back,ops) }
      , "Delayed current goal")
    | _ -> tacerror "last: no goals"
    end

  | PT.Admit ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_,_,_) ->
      ({ts with ts_ps =
          ActiveProof(first (CR.apply_first (CR.t_admit "") ps),[],mempty,Some(ps))}
      , "Admit goal.")
    | _ -> tacerror "admit: no goals"
    end

  | PT.PrintGoals(s) ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) ->
      let msg = fsprintf "@[<v>Proof state %s:@\n%a@]" s (pp_jus 100) ps.CR.subgoals in
      (ts, msg)
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Theory closed.")
    end

  | PT.PrintProof(verbose,mfile) ->
    begin match ts.ts_ps with
    | BeforeProof -> (ts, "No proof started yet.")
    | ActiveProof _ | ClosedTheory _ ->
      let pt =
        match ts.ts_ps with
        | BeforeProof -> assert false
        | ClosedTheory pt          -> pt
        | ActiveProof  (ps,_,_,_)  -> CR.get_proof (prove_by_admit "" ps)
      in
      let pt = simplify_proof_tree pt |> decorate_proof_tree in
      let buf = Buffer.create 1024 in
      let fbuf = F.formatter_of_buffer buf in
      F.pp_set_margin fbuf 240;
      F.fprintf fbuf "%a" (pp_proof_tree pp_path verbose) pt;
      (match mfile with
       | Some filename ->
         let out = open_out filename in
         let fmt = F.formatter_of_out_channel out in
         F.pp_set_margin fmt 240;
         F.fprintf fmt "%a" (pp_proof_tree pp_path verbose) pt;
         close_out out
       | None -> ());
      (ts, Buffer.contents buf)
    end

  | PT.PrintGoal(s) ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) ->
      let msg = fsprintf "Current goal in state %s:%a@."
        s
        (pp_jus 100)
        (Util.take 1 ps.CR.subgoals)
      in
      (ts, msg)
    | BeforeProof  -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Proof finished.")
    end

  | PT.Restart ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) ->
      let _prf = CR.get_proof (prove_by_admit "" ps) in
      ({ts with ts_ps = ClosedTheory (ps.CR.validation [])}, "Restarted proof.")
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Proof finished.")
    end

  | PT.Qed ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) ->
      if ps.CR.subgoals = [] then
        ({ts with ts_ps = ClosedTheory (ps.CR.validation [])}, "Finished proof.")
      else
        tacerror "Cannot finish proof, open goals."
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Proof finished.")
    end

  | PT.Extract filename ->
    Extraction.extract ts filename;
    (ts, "EasyCrypt proof script extracted into file: "^filename)

  | PT.PrintGame filename ->
    let ps = get_proof_state ts in
    let ju = match ps.CR.subgoals with
      | ju::_ -> ju
      | []    -> tacerror "cannot print game: there is no goal"
    in
    output_file filename (fsprintf "%a" pp_se_nonum ju.ju_se);
    (ts, "Current game printed into file: "^filename)

  | PT.PrintGames(fn1,fn2) ->
    let ps = get_proof_state ts in
    let se1,se2 = match ps.CR.subgoals with
      | ju::_ ->
        begin match ju.ju_pr with
        | Pr_Dist se2 -> (ju.ju_se,se2)
        | _ -> tacerror "cannot print game: judgment of wrong type"
        end
      | [] -> tacerror "cannot print games: there is no goal"
    in
    ExprUtils.pp_sort_expensive := true;
    ExprUtils.pp_number_tuples := true;
    output_file fn1 (fsprintf "%a" pp_se_nonum se1);
    output_file fn2 (fsprintf "%a" pp_se_nonum se2);
    ExprUtils.pp_sort_expensive := false;
    ExprUtils.pp_number_tuples := false;
    (ts, F.sprintf "Current games printed into files: %s and %s" fn1 fn2)

  | PT.Debug cmd ->
    begin match cmd with
    | "cases" ->
      CaseRules.print_cases ts
    | "alternatives" ->
      begin match ts.ts_ps with
      | ActiveProof(_,_,back,_) ->
        (ts, F.sprintf "There are %i alternatives left." (L.length (run (-1) back)))
      | BeforeProof  -> (ts, "No proof started yet.")
      | ClosedTheory _ -> (ts, "Proof finished.")
      end

    | _ ->
      tacerror "Unknown debug command."
    end

let handle_instrs verbose ts instrs =
  L.fold_left (fun (ts,s) instr ->
    let (ts',s') = handle_instr verbose ts instr in
    (ts',s^"\n"^s'))
    (ts,"")
    instrs

let eval_theory s =
  let pt = Parse.theory s in
  let empty_ts = mk_ts () in
  L.fold_left
    (fun ps i ->
      let (ps', s) = handle_instr false ps i in
      print_endline s;
      ps')
    empty_ts
    pt
