(*s Tactic engine: transformations of theory and proof states. *)

(*i*)
open Abbrevs
open Expr
open ExprUtils
open Type
open Util
open Nondet
open Syms
open Gsyms
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
module G = Game
module CR = CoreRules

let log_i ls = mk_logger "Norm" Bolt.Level.INFO "NormField" ls
(*i*)


(*i ----------------------------------------------------------------------- i*)
(* \hd{Utility functions} *)

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
  if i < 1 then L.length ju.ju_se.se_gdef + i + 1 else i

let epos_of_offset ju i =
  let ev = ju.ju_se.se_ev in
  if i < 1 && is_Land ev
  then L.length (destr_Land ev) + i + 1
  else i

let gpos_of_apos ju ap =
  let module E = struct exception Found of int end in
  let find s i cmd =
    match cmd with
    | GLet(vs,_) | GSamp(vs,_)
      when s = Id.name vs.Vsym.id -> raise (E.Found i)
    | _ -> ()
  in
  match ap with
  | PT.Var s ->
    begin try
      L.iteri (find s) ju.ju_se.se_gdef;
      tacerror "variable not found in game"
    with
      E.Found i -> i
    end
  | PT.Pos i -> gpos_of_offset ju i

(*i ----------------------------------------------------------------------- i*)
(* \hd{Tactic handling} *)

let handle_tactic ts tac =
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
      | Left None     -> tacerror "mempty"
      | Left (Some s) -> tacerror "%s" (Lazy.force s)
      | Right(nps,pss) ->
        let ops = Some ps in
        let ts' = { ts with ts_ps = ActiveProof(nps,[],pss,ops) } in
        (ts', lazy (diff_step ops nps))
      end
    with
    | Wf.Wf_div_zero es ->
      tacerror "Wf: Cannot prove that %a nonzero" (pp_list "," pp_exp) es
    | Wf.Wf_var_undef(v,e) ->
      tacerror "Wf: Var %a undefined in %a" Vsym.pp v pp_exp e
  in
  let vmap_g = vmap_of_globals ju.ju_se.se_gdef in
  let e_pos = epos_of_offset ju in
  let t_pos = gpos_of_offset ju in
  let get_pos = gpos_of_apos ju in
  let parse_e se = PU.expr_of_parse_expr vmap_g ts se in
  let mk_new_var sv ty = assert (not (Ht.mem vmap_g sv)); Vsym.mk sv ty in
  match tac with
  (* Rules with primitive arguments *)
  | PT.Rnorm                 -> apply t_norm
  | PT.Rnorm_nounfold        -> apply t_norm_nounfold
  | PT.Rlet_unfold(Some(i))  -> apply (t_let_unfold (get_pos i))
  | PT.Rlet_unfold(None)     -> apply (t_unfold_only)
  | PT.Rswap(i,j)            -> apply (CR.t_swap (t_pos i) j)
  | PT.Rremove_ev(is)        -> apply (CR.t_remove_ev is)
  | PT.Rsplit_ev(i)          -> apply (CR.t_split_ev (e_pos i))
  | PT.Rrewrite_ev(i,d)      -> apply (CR.t_rw_ev (e_pos i) d)
  | PT.Rcrush(finish,mi)     -> apply (t_crush finish mi ts ps)

  | PT.Rcase_ev(Some(se)) ->
    apply (CR.t_case_ev (parse_e se))

  | PT.Rsubst(i,e1,e2,mupto) ->
    apply (t_subst (t_pos i) (parse_e e1) (parse_e e2) mupto)

  | PT.Rcase_ev(None) ->
    apply t_case_ev_maybe

  | PT.Rexcept(Some(i),Some(ses)) ->
    apply (CR.t_except (get_pos i) (L.map (parse_e) ses))
  | PT.Rexcept(i,ses) ->
    apply (t_rexcept_maybe (map_opt get_pos i) ses)

  | PT.Rswap_oracle(op,j)    -> apply (CR.t_swap_oracle op j)
  | PT.Rrewrite_orcl(op,dir) -> apply (CR.t_rewrite_oracle op dir)

  | PT.Rfalse_ev             -> apply CR.t_false_ev
  | PT.Rindep(exact)         -> apply (t_random_indep exact)

  | PT.Rnorm_unknown(is) ->
    let vs = L.map (fun s -> mk_V (Ht.find vmap_g s)) is in
    apply (t_norm_unknown vs)

  | PT.Rlet_abstract(Some(i),sv,Some(se),mupto,no_norm) ->
    let e = parse_e se in
    let v = mk_new_var sv e.e_ty in
    apply (t_let_abstract (t_pos i) v e (map_opt t_pos mupto) (not no_norm))

  | PT.Rlet_abstract(None,sv,None,mupto,no_norm) ->
    let v = mk_new_var sv ju.ju_se.se_ev.e_ty in
    let max = L.length ju.ju_se.se_gdef in
    apply (t_let_abstract max v ju.ju_se.se_ev (map_opt t_pos mupto) (not no_norm))

  | PT.Rlet_abstract(_,_,_,_,_) ->
    tacerror "No placeholders or placeholders for both position and event"

  | PT.Requiv(sgd,sev) ->
    let vmap2 = Hashtbl.create 134 in
    let gd2 = PU.gdef_of_parse_gdef vmap2 ts sgd in
    let ev2 = PU.expr_of_parse_expr vmap2 ts sev in
    apply (CR.t_conv true ~do_rename:true { se_gdef = gd2; se_ev = ev2 })

  | PT.Rassm_dec(exact,maname,mdir,mrngs,msvs) ->
    apply (t_assm_dec ts exact maname mdir mrngs msvs)

  | PT.Rnorm_solve(se) ->
    let e = parse_e se in
    apply (RewriteRules.t_norm_solve e)

  | PT.Rexcept_orcl(op,pes) ->
    let vmap = vmap_in_orcl ju.ju_se op in
    let es = L.map (PU.expr_of_parse_expr vmap ts) pes in
    apply (CR.t_except_oracle op es)

  | PT.Rctxt_ev (mj,Some(sv,e)) ->
    let j = match mj with
      | Some j -> j
      | None -> tacerror "position placeholder not allowed if context is given"
    in
    let ev = ju.ju_se.se_ev in
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
    let vmap = vmap_of_globals ju.ju_se.se_gdef in
    let v1 = PU.create_var vmap sv ty in
    let e1 = PU.expr_of_parse_expr vmap ts e in
    let c = v1, e1 in
    apply (CR.t_ctxt_ev j c)

  | PT.Rctxt_ev (mj,None) ->
    apply (SimpRules.t_ctx_ev_maybe mj)

  | PT.Rsimp must_finish ->
    apply (SimpRules.t_simp must_finish 20 ts)

  | PT.Rassm_comp(exact,maname,mrngs) ->
    apply (t_assm_comp ts exact maname mrngs)

  | PT.Rrnd(exact,mi,mctxt1,mctxt2,mgen) ->
    let mgen = map_opt parse_e mgen in
    apply (t_rnd_maybe ts exact (map_opt get_pos mi) mctxt1 mctxt2 mgen)

  | PT.Rrnd_orcl(mopos,mctxt1,mctxt2) ->
    apply (t_rnd_oracle_maybe ts mopos mctxt1 mctxt2)

  | PT.Radd_test(Some(opos),Some(t),Some(aname),Some(fvs)) ->
    (* create symbol for new adversary *)
    let se = ju.ju_se in
    let _, seoc = get_se_octxt se opos in
    let vmap = vmap_in_orcl se opos in
    let t = PU.expr_of_parse_expr vmap ts t in
    let oasym = seoc.seoc_asym in
    let oty = seoc.seoc_osym.Osym.dom in
    let destr_prod ty = match oty.ty_node with
      | Prod(tys) -> tys
      | _ -> [ty]
    in
    fail_unless (fun () -> not (Mstring.mem aname ts.ts_adecls))
      "radd_test: adversary with same name already declared";
    let asym = Asym.mk aname oasym.Asym.dom oty in
    let adecls = Mstring.add aname asym ts.ts_adecls in
    let tys = destr_prod oty in
    (* create variables for returned values *)
    fail_unless (fun () -> L.length fvs = L.length tys)
      "number of given variables does not match type";
    let fvs = L.map2 (fun v ty -> PU.create_var vmap v ty) fvs tys in
    apply ~adecls (CR.t_add_test opos t asym fvs)

  | PT.Radd_test(None,None,None,None) ->
    apply t_add_test_maybe

  | PT.Radd_test(_,_,_,_) ->
    tacerror "radd_test expects either all values or only placeholders"

  | PT.Rbad(i,sx) ->
    let ty =
      match get_se_gcmd ju.ju_se i with
      | G.GLet(_,e') when is_H e' ->
        let _,e = destr_H e' in
        e.e_ty
      | _ -> tacerror "Line %is not hash assignment." i
    in
    let vx = PU.create_var (vmap_of_globals ju.ju_se.se_gdef) sx ty in
    apply (CR.t_bad (t_pos i) vx)

  | PT.Deduce(pes,pe) ->
    let es = L.map (PU.expr_of_parse_expr vmap_g ts) pes in
    let e = PU.expr_of_parse_expr vmap_g ts  pe in
    log_i (lazy (fsprintf "deduce %a |- %a@\n" (pp_list "," pp_exp) es pp_exp e));
    (try
       let frame =
         L.mapi
           (fun i e -> (e, I (mk_V (Vsym.mk ("x"^(string_of_int i)) e.e_ty))))
           es
       in
       let recipe = Deduc.invert frame e in
       log_i (lazy (fsprintf "Found %a@\n" pp_exp recipe))
     with
       Not_found ->
         tacerror "Not found@\n");
    (ts,lazy "")

  | PT.FieldExprs(pes) ->
    let es = L.map (PU.expr_of_parse_expr vmap_g ts) pes in
    let ses = ref Se.empty in
    Game.iter_se_exp ~iexc:true
      (fun e' -> e_iter_ty_maximal mk_Fq
        (fun fe -> if L.exists (fun e -> e_exists (e_equal e) fe) es then ses := Se.add fe !ses) e')
      ju.ju_se;
    let res = (lazy (fsprintf "field expressions with %a: @\n@[<hov 2>  %a@]"
                       (pp_list ", " pp_exp) es (pp_list ",@\n" pp_exp) (Se.elements !ses))) in
    log_i res;
    (ts,res)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Instruction handling} *)

let handle_instr verbose ts instr =
  match instr with
  | PT.RODecl(s,ro,t1,t2) ->
    let oname = if ro then "random oracle" else "operator" in
    if Mstring.mem s ts.ts_rodecls then
      tacerror "%s with same name already declared." oname;
    let hs = Hsym.mk s ro (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2) in
    let ts = { ts with ts_rodecls = Mstring.add s hs ts.ts_rodecls } in
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
    (ts, "Declared oracle.")

  | PT.ADecl(s,t1,t2) ->
    if Mstring.mem s ts.ts_adecls then
      tacerror "adversary with same name already declared.";
    let asym = Asym.mk s (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2) in
    let ts = { ts with ts_adecls = Mstring.add s asym ts.ts_adecls } in
    (ts, "Declared adversary.")

  | PT.AssmDec(s,g0,g1,symvs) ->
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
    if Mstring.mem s ts.ts_assms_dec then
      tacerror "assumption with the same name already exists";
    let ts = {
      ts with
        ts_assms_dec =
        Mstring.add s (Assumption.mk_assm_dec s g0 g1 symvs) ts.ts_assms_dec
    }
    in
    (ts, "Declared decisional assumption.")

  | PT.AssmComp(s,g,ev,symvs) ->
    let vmap = Ht.create 137 in
    let g = PU.gdef_of_parse_gdef vmap ts g in
    let parse_var s =
      try  Ht.find vmap s
      with Not_found -> tacerror "unknown variable %s" s
    in
    let symvs = L.map (L.map parse_var) symvs in
    let ev = PU.expr_of_parse_expr vmap ts ev in
    let assm = Assumption.mk_assm_comp s g ev symvs in
    if Mstring.mem s ts.ts_assms_comp then
      tacerror "assumption with the same name already exists";
    let ts = { ts with ts_assms_comp = Mstring.add s assm ts.ts_assms_comp } in
    (ts, "Declared computational assumption.")

  | PT.Judgment(gd,e) ->
    let vmap = Ht.create 137 in
    let se = PU.se_of_parse_se vmap ts gd e in
    let ju = { ju_se = se; ju_pr = Pr_Adv } in
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

  | PT.PrintProof(verbose) ->
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
