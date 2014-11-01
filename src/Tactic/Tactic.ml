(*s Tactic engine: transformations of theory and proof states. *)

(*i*)
open Expr
open Type
open Util
open Nondet
open Syms
open Gsyms
open TheoryState
open Rules
open RewriteRules
open AssumptionRules
open RandomRules
open RindepRules
open CrushRules
open CaseRules
open Game

module Ht = Hashtbl
module PU = ParserUtil
module G = Game
module CR = CoreRules
(*i*)


let fail_unless c s =
  if not (c ()) then tacerror s

let diff_step ops nps =
  match ops with
  | Some ops ->
    let get_pt ps = CR.get_proof (prove_by_admit "" ps) |> simplify_proof_tree in
    fsprintf "@\n  @[%a@]"
      (pp_list "@\n" (pp_proof_tree ~hide_admit:true false))
      (diff_proof_tree (get_pt ops,get_pt nps))
  | None -> ""

let handle_tactic ts tac =
  let ps = get_proof_state ts in
  let ju = match ps.CR.subgoals with
    | ju::_ -> ju
    | []    -> tacerror "cannot apply tactic: there is no goal"
  in
  let apply ?adecls r =
    try
      let ts =
        match adecls with
        | None   -> ts
        | Some ad -> { ts with ts_adecls = ad }
      in
      let pss = CR.apply_first r ps in
      begin match pull pss with
      | Left None     -> tacerror "mempty"
      | Left (Some s) -> tacerror "%s" s
      | Right(ps,pss) ->
        let ops = Some (get_proof_state ts) in
        let ts' = { ts with ts_ps = ActiveProof(ps,[],pss,ops) } in
        (ts', diff_step ops ps)
      end
    with
    | Wf.Wf_div_zero es ->
      tacerror "Wf: Cannot prove that %a nonzero" (pp_list "," pp_exp) es
    | Wf.Wf_var_undef(v,e) ->
      tacerror "Wf: Var %a undefined in %a" Vsym.pp v pp_exp e
  in
  let vmap_g = vmap_of_globals ju.ju_gdef in
  let parse_e se = PU.expr_of_parse_expr vmap_g ts se in
  let mk_new_var sv ty =
    assert (not (Ht.mem vmap_g sv));
    Vsym.mk sv ty
  in
  match tac with
  (* Rules with primitive arguments *)
  | PU.Rnorm                 -> apply t_norm
  | PU.Rnorm_nounfold        -> apply t_norm_nounfold
  | PU.Rlet_unfold(i)        -> apply (t_let_unfold i)
  | PU.Rswap(i,j)            -> apply (CR.t_swap i j)
  | PU.Rremove_ev(is)        -> apply (CR.t_remove_ev is)
  | PU.Rsplit_ev(i)          -> apply (CR.t_split_ev i)
  | PU.Rrewrite_ev(i,d)      -> apply (CR.t_rw_ev i d)
  | PU.Rcrush(finish,mi)     -> apply (t_crush finish mi ts ps)

  | PU.Rcase_ev(Some(se)) ->
    apply (CR.t_case_ev (parse_e se))

  | PU.Rcase_ev(None) ->
    apply t_case_ev_maybe

  | PU.Rexcept(Some(i),Some(ses)) ->
    apply (CR.t_except i (L.map (parse_e) ses))
  | PU.Rexcept(i,ses) ->
    apply (t_rexcept_maybe i ses)

  | PU.Rswap_oracle(op,j)    -> apply (CR.t_swap_oracle op j)
  | PU.Rrewrite_orcl(op,dir) -> apply (CR.t_rewrite_oracle op dir)

  | PU.Rfalse_ev             -> apply CR.t_false_ev
  | PU.Rindep(exact)         -> apply (t_random_indep exact)

  | PU.Rnorm_unknown(is) ->
    let vs = L.map (fun s -> mk_V (Ht.find vmap_g s)) is in
    apply (t_norm_unknown vs)

  | PU.Rlet_abstract(i,sv,se,mupto) ->
    let e = parse_e se in
    let v = mk_new_var sv e.e_ty in
    apply (t_let_abstract i v e mupto)

  | PU.Requiv(sgd,sev) ->
    let vmap2 = Hashtbl.create 134 in
    let gd2 = PU.gdef_of_parse_gdef vmap2 ts sgd in
    let ev2 = PU.expr_of_parse_expr vmap2 ts sev in
    apply (CR.t_conv true ~do_rename:true { ju_gdef = gd2; ju_ev = ev2 })

  | PU.Rassm_dec(exact,maname,mdir,mrngs,msvs) ->
    apply (t_assm_dec ts exact maname mdir mrngs msvs)

  | PU.Rnorm_solve(se) ->
    let e = parse_e se in
    apply (RewriteRules.t_norm_solve e)

  | PU.Rexcept_orcl(_op,_es) ->
    failwith "undefined"
    (*i
    let es = L.map (PU.expr_of_parse_expr ts) es in
    apply_rule (t_except_oracle op es) ts
    i*)

  | PU.Rctxt_ev (sv,e,j) ->
    let ev = ju.ju_ev in
    let b =
      match ev.e_node with
      | Nary(Land,es) when j < L.length es ->
        L.nth es j
      | _ when j = 0 -> ev
      | _ -> tacerror "rctxt_ev: bad index"
    in
    let ty = 
      if is_Eq b then (fst (destr_Eq b)).e_ty
      else if is_Exists b then
        let (e1,_,_) = destr_Exists b in e1.e_ty 
      else tacerror "rctxt_ev: bad event"
    in
    let vmap = vmap_of_globals ju.ju_gdef in
    let v1 = PU.create_var vmap sv ty in
    let e1 = PU.expr_of_parse_expr vmap ts e in
    let c = v1, e1 in
    apply (CR.t_ctxt_ev j c)

  | PU.Rsimp ->
    apply (t_simp false 20 ts)

  | PU.Rassm_comp(exact,maname,mev_e) ->
    apply (t_assm_comp ts exact maname mev_e)

  | PU.Rrnd(exact,mi,mctxt1,mctxt2) ->
    apply (t_rnd_maybe ts exact mi mctxt1 mctxt2)

  | PU.Rrnd_orcl(mopos,mctxt1,mctxt2) ->
    apply (t_rnd_oracle_maybe ts mopos mctxt1 mctxt2)
   
  | PU.Radd_test(Some(opos),Some(t),Some(aname),Some(fvs)) ->
    (* create symbol for new adversary *)
    let _, juoc = get_ju_octxt ju opos in
    let vmap = vmap_in_orcl ju opos in
    let t = PU.expr_of_parse_expr vmap ts t in
    let oasym = juoc.juoc_asym in
    let oty = juoc.juoc_osym.Osym.dom in
    let destr_prod ty = match oty.ty_node with
      | Prod(tys) -> tys
      | _ -> [ty]
    in
    fail_unless (fun () -> not (Ht.mem ts.ts_adecls aname))
      "radd_test: adversary with same name already declared";
    let asym = Asym.mk aname oasym.Asym.dom oty in
    let adecls = Ht.copy ts.ts_adecls in
    Ht.add adecls aname asym;
    let tys = destr_prod oty in
    (* create variables for returned values *)
    fail_unless (fun () -> L.length fvs = L.length tys)
      "number of given variables does not match type";
    let fvs = L.map2 (fun v ty -> PU.create_var vmap v ty) fvs tys in
    apply ~adecls (CR.t_add_test opos t asym fvs)

  | PU.Radd_test(None,None,None,None) ->
    apply t_add_test_maybe

  | PU.Radd_test(_,_,_,_) ->
    tacerror "radd_test expects either all values or only placeholders"

  | PU.Rbad(i,sx) ->
    let ty =
      match get_ju_gcmd ju i with
      | G.GLet(_,e') when is_H e' ->
        let _,e = destr_H e' in
        e.e_ty
      | _ -> tacerror "Line %is not hash assignment." i
    in
    let vx = PU.create_var (vmap_of_globals ju.ju_gdef) sx ty in
    apply (CR.t_bad i vx)

  | PU.Deduce(pes,pe) ->
    let es = L.map (PU.expr_of_parse_expr vmap_g ts) pes in
    let e = PU.expr_of_parse_expr vmap_g ts  pe in
    eprintf "deduce %a |- %a@\n" (pp_list "," pp_exp) es pp_exp e;
    (try
       let frame =
         L.mapi
           (fun i e -> (e, I (mk_V (Vsym.mk ("x"^(string_of_int i)) e.e_ty))))
           es
       in
       let recipe = Deduc.invert frame e in
       eprintf "Found %a@\n" pp_exp recipe
     with
       Not_found ->
         tacerror "Not found@\n");
    (ts,"")

let pp_jus i fmt jus =  
  match jus with
  | [] -> F.printf "No remaining goals, proof completed.@\n"
  | jus ->
    let n = L.length jus in
    let goal_num = if n = 1 then "" else F.sprintf " (of %i)" n in
    let pp_goal i ju =
      F.fprintf fmt "goal %i%s:@\n%a@\n@\n" (i + 1) goal_num pp_ju ju
    in
    L.iteri pp_goal (Util.take i jus)

let handle_instr ts instr =
  match instr with
  | PU.RODecl(s,ro,t1,t2) ->
    let oname = if ro then "random oracle" else "operator" in
    if Ht.mem ts.ts_rodecls s then
      tacerror "%s with same name already declared." oname;
    Ht.add ts.ts_rodecls s
      (Hsym.mk s ro (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2));
    (ts, fsprintf "Declared %s" oname)

  | PU.EMDecl(s,g1,g2,g3) ->
    if Ht.mem ts.ts_emdecls s then
      tacerror "Bilinear map with same name already declared.";
    Ht.add ts.ts_emdecls s
      (Esym.mk s (create_groupvar ts g1) (create_groupvar ts g2) (create_groupvar ts g3));
    (ts, "Declared bilinear map.")

  | PU.ODecl(s,t1,t2) ->
      if Ht.mem ts.ts_odecls s then 
        tacerror "Oracle with same name already declared.";
    Ht.add ts.ts_odecls s 
      (Osym.mk s (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2));
    (ts, "Declared oracle.")

  | PU.ADecl(s,t1,t2) ->
    if Ht.mem ts.ts_adecls s then 
      tacerror "adversary with same name already declared.";
    Ht.add ts.ts_adecls s 
      (Asym.mk s (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2));
    (ts, "Declared adversary.")

  | PU.AssmDec(s,g0,g1,symvs) ->
    let vmap1 = Ht.create 137 in
    let vmap2 = Ht.create 137 in
    let g0 = PU.gdef_of_parse_gdef vmap1 ts g0 in
    let g1 = PU.gdef_of_parse_gdef vmap2 ts g1 in
    let vmap, sigma = merge_vmap vmap1 vmap2 in
    let g1 = subst_v_gdef sigma g1 in
    let parse_var s =
      try  Ht.find vmap s
      with Not_found -> tacerror "unknown variable %s" s
    in
    let symvs = L.map (L.map parse_var) symvs in
    if Ht.mem ts.ts_assms_dec s then
      tacerror "assumption with the same name already exists";
    Ht.add ts.ts_assms_dec s (Assumption.mk_assm_dec s g0 g1 symvs);
    (ts, "Declared decisional assumption.")

  | PU.AssmComp(s,g,ev_var,ev_ty,ev,privs,symvs) ->
    let vmap = Ht.create 137 in
    let g = PU.gdef_of_parse_gdef vmap ts g in
    let parse_var s =
      try  Ht.find vmap s
      with Not_found -> tacerror "unknown variable %s" s
    in
    let priv = Vsym.set_of_list (L.map parse_var privs) in
    let symvs = L.map (L.map parse_var) symvs in
    let ev_ty  = PU.ty_of_parse_ty ts ev_ty in
    let ev_var = PU.create_var vmap ev_var ev_ty in
    let ev = PU.expr_of_parse_expr vmap ts ev in
    let assm = Assumption.mk_assm_comp s g ev_var ev priv symvs in
    if Ht.mem ts.ts_assms_comp s then
      tacerror "assumption with the same name already exists";
    Ht.add ts.ts_assms_comp s assm;
    (ts, "Declared computational assumption.")
    
  | PU.Judgment(gd,e) ->
    let vmap = Ht.create 137 in
    let ju = PU.ju_of_parse_ju vmap ts gd e in
    let ps = first (CR.t_id ju) in
    ({ ts with ts_ps = ActiveProof(ps,[],mempty,None) }
    , "Started proof of judgment.")

  | PU.Apply(tac) ->
    let (ts,s) = handle_tactic ts tac in
    (ts, "Applied tactic: "^s)

  | PU.Back ->
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

  | PU.UndoBack(false) ->
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

  | PU.UndoBack(true) ->
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

  | PU.Last ->
    begin match ts.ts_ps with
    | ActiveProof(ps,uback,back,ops) -> 
      ({ ts with ts_ps = ActiveProof(CR.move_first_last ps,uback,back,ops) }
      , "Delayed current goal")
    | _ -> tacerror "last: no goals"
    end

  | PU.Admit ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_,_,_) -> 
      ({ts with ts_ps =
          ActiveProof(first (CR.apply_first (CR.t_admit "") ps),[],mempty,Some(ps))}
      , "Admit goal.")
    | _ -> tacerror "admit: no goals"
    end

  | PU.PrintGoals(s) ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) -> 
      let msg = fsprintf "@[<v>Proof state %s:@\n%a@]" s (pp_jus 100) ps.CR.subgoals in
      (ts, msg)
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Theory closed.")
    end

  | PU.PrintProof(verbose) ->
    begin match ts.ts_ps with
    | BeforeProof -> (ts, "No proof started yet.")
    | ActiveProof _ | ClosedTheory _ ->
      let pt =
        match ts.ts_ps with
        | BeforeProof -> assert false
        | ClosedTheory pt          -> pt
        | ActiveProof  (ps,_,_,_)  -> CR.get_proof (prove_by_admit "" ps)
      in
      let pt = simplify_proof_tree pt in
      let buf = Buffer.create 1024 in
      let fbuf = F.formatter_of_buffer buf in
      F.pp_set_margin fbuf 240;
      F.fprintf fbuf "%a" (pp_proof_tree verbose) pt;
      (ts, Buffer.contents buf)
    end

  | PU.PrintGoal(s) ->
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

  | PU.Qed ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_uback,_back,_) ->
      if ps.CR.subgoals = [] then
        ({ts with ts_ps = ClosedTheory (ps.CR.validation [])}, "Finished proof.")
      else
        tacerror "Cannot finish proof, open goals."
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Proof finished.")
    end

  | PU.Extract filename ->
    Extraction.extract ts filename;
    (ts, "EasyCrypt proof script extracted into file: "^filename)

  | PU.Debug cmd ->
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

let eval_theory s =
  let pt = Parse.theory s in
  let empty_ts = mk_ts () in
  L.fold_left
    (fun ps i ->
      let (ps', s) = handle_instr ps i in
      print_endline s;
      ps')
    empty_ts
    pt

