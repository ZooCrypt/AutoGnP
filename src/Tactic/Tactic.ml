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
open CrushRules
open Game

module Ht = Hashtbl
module PU = ParserUtil
module G = Game
module CR = CoreRules
(*i*)


let fail_unless c s =
  if not (c ()) then tacerror s

(*i 
let rec simp_event ts =
  let g = get_proof_state ts in
  let apply_rule r ts = { ts with ts_ps = ActiveProof(t_first r g) } in
  let ju = match g.subgoals with
    | ju::_ -> ju
    | []    -> tacerror "cannot apply tactic: there is no goal"
  in
  (* FIXME: for now, we just clean up ts_vars here *)
  let ts = ts_importvars ts ju in
  
  let 
  let ev = ju.Game.ju_ev in
    let i = ref (-1) in
    let tac =
      if is_Land ev then (
        L.fold_left
          (fun t e ->
             i := !i + 1;
             if is_Eq e then (
               let (a,b) = destr_Eq e in
               if is_V a then (
                 F.printf "%i %a ->\n%!" !i pp_exp e;
                 (t @. t_rw_ev !i LeftToRight)
               ) else if is_V b then (
                 F.printf "%i %a <-\n%!" !i pp_exp e;
                 (t @. t_rw_ev !i RightToLeft)
               ) else if is_Tuple a && is_Tuple b then (
                 F.printf "%i splitting %a \n%!" !i pp_exp e;
                 (t @. t_split_ev !i)                        
               ) else (
                 F.printf "%i no V %a \n%!" !i pp_exp e;
                 t
               )
             ) else (
               F.printf "%i no eq %a \n%!" !i pp_exp e;
               t
             )
          )
          t_id
          (destr_Land ev)
      ) else (
        t_id
      )
    in
    (* { ts with ts_ps = ActiveProof(t_first r g) } in *)
    apply_rule (tac @. t_norm @. t_false_ev) ts
i*)  

let handle_tactic ts tac =
  let ps = get_proof_state ts in
  let ju = match ps.CR.subgoals with
    | ju::_ -> ju
    | []    -> tacerror "cannot apply tactic: there is no goal"
  in
  let apply r =
    let pss = CR.apply_first r ps in
    match pull pss with
    | Left None -> tacerror "mempty"
    | Left (Some s) -> tacerror "%s" s
    | Right(ps,pss) ->
      { ts with ts_ps = ActiveProof(ps,pss) }
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
  | PU.Rexcept(i,ses)        -> apply (CR.t_except i (L.map (parse_e) ses))
  | PU.Rremove_ev(is)        -> apply (CR.t_remove_ev is)
  | PU.Rsplit_ev(i)          -> apply (CR.t_split_ev i)
  | PU.Rrewrite_ev(i,d)      -> apply (CR.t_rw_ev i d)
  | PU.Rcase_ev(se)          -> apply (CR.t_case_ev (parse_e se))
  | PU.Rcrush(finish,mi)     -> apply (t_crush finish mi ts ps)

  | PU.Rswap_oracle(op,j)    -> apply (CR.t_swap_oracle op j)
  | PU.Rrewrite_orcl(op,dir) -> apply (CR.t_rewrite_oracle op dir)

  | PU.Rfalse_ev             -> apply CR.t_false_ev
  | PU.Rindep                -> apply t_random_indep

  | PU.Rnorm_unknown(is) ->
    let vs = L.map (fun s -> mk_V (Ht.find vmap_g s)) is in
    apply (t_norm_unknown vs)

  | PU.Rlet_abstract(i,sv,se) ->
    let e = parse_e se in
    let v = mk_new_var sv e.e_ty in
    apply (t_let_abstract i v e)

  | PU.Requiv(sgd,sev) ->
    let vmap2 = Hashtbl.create 134 in
    let gd2 = PU.gdef_of_parse_gdef vmap2 ts sgd in
    let ev2 = PU.expr_of_parse_expr vmap2 ts sev in
    apply (CR.t_conv true { ju_gdef = gd2; ju_ev = ev2 })

  | PU.Rassm_dec(maname,mdir,msvs) ->
    apply (t_assm_dec ts maname mdir msvs)

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

  | PU.Rsimp -> tacerror "not implemented"

  | PU.Rassm_comp(s,ev_e) ->
    let assm = 
      try Ht.find ts.ts_assms_comp s 
      with Not_found -> tacerror "error no assumption %s" s
    in
    let vmap = vmap_of_globals ju.ju_gdef in
    let ev_e = PU.expr_of_parse_expr vmap ts ev_e in
    apply (t_assm_comp assm ev_e)

  | PU.Rrnd(mi,mctxt1,mctxt2) ->
    apply (t_rnd_maybe ts mi mctxt1 mctxt2)

  | PU.Rrnd_orcl(mopos,mctxt1,mctxt2) ->
    apply (t_rnd_oracle_maybe ts mopos mctxt1 mctxt2)
   
  | PU.Radd_test(op,t,aname,fvs) ->
    let _, juoc = get_ju_octxt ju op in
    let vmap = vmap_in_orcl ju op in
    let t = PU.expr_of_parse_expr vmap ts t in
    let oty = juoc.juoc_osym.Osym.dom in
    let destr_prod ty = match oty.ty_node with
      | Prod(tys) -> tys
      | _ -> [ty]
    in
    fail_unless (fun () -> not (Ht.mem ts.ts_adecls aname))
      "radd_test: adversary with same name already declared";
    let asym = Asym.mk aname (mk_Prod []) oty in
    Ht.add ts.ts_adecls aname asym;
    let tys = destr_prod  oty in
    fail_unless (fun () -> L.length fvs = L.length tys)
      "number of given variables does not match type";
    let fvs = L.map2 (fun v ty -> PU.create_var vmap v ty) fvs tys in
    apply (CR.t_add_test op t asym fvs)

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

let pp_jus fmt jus =  
  match jus with
  | [] -> F.printf "No remaining goals, proof completed.@\n"
  | jus ->
    let pp_goal i ju =
      F.fprintf fmt "goal %i:@\n%a@\n@\n" (i + 1) pp_ju ju in
    L.iteri pp_goal jus 


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

  | PU.AssmDec(s,g0,g1,priv) ->
    let vmap1 = Ht.create 137 in
    let vmap2 = Ht.create 137 in
    let g0 = PU.gdef_of_parse_gdef vmap1 ts g0 in
    let g1 = PU.gdef_of_parse_gdef vmap2 ts g1 in
    let vmap, sigma = merge_vmap vmap1 vmap2 in
    let g1 = subst_v_gdef sigma g1 in
    let priv =
      L.fold_left
        (fun s x -> 
          try  Vsym.S.add (Ht.find vmap x) s
          with Not_found -> tacerror "unknown variable %s" x)
        Vsym.S.empty
        priv
    in
    if Ht.mem ts.ts_assms_dec s then
      tacerror "assumption with the same name already exists";
    Ht.add ts.ts_assms_dec s (Assumption.mk_assm_dec s g0 g1 priv);
    (ts, "Declared decisional assumption.")

  | PU.AssmComp(s,g,ev_var,ev_ty,ev,priv) ->
    let vmap = Ht.create 137 in
    let g = PU.gdef_of_parse_gdef vmap ts g in
    let priv =
      L.fold_left
        (fun s x -> 
          try  Vsym.S.add (Ht.find vmap x) s
          with Not_found -> tacerror "unknown variable %s" x)
        Vsym.S.empty
        priv
    in
    let ev_ty  = PU.ty_of_parse_ty ts ev_ty in
    let ev_var = PU.create_var vmap ev_var ev_ty in
    let ev = PU.expr_of_parse_expr vmap ts ev in
    let assm = Assumption.mk_assm_comp s g ev_var ev priv in
    if Ht.mem ts.ts_assms_comp s then
      tacerror "assumption with the same name already exists";
    Ht.add ts.ts_assms_comp s assm;
    (ts, "Declared computational assumption.")
    
  | PU.Judgment(gd, e) ->
    let vmap = Ht.create 137 in
    let ju = PU.ju_of_parse_ju vmap ts gd e in
    ({ ts with ts_ps = ActiveProof(first (CR.t_id ju),mempty) }
    , "Started proof of judgment.")

  | PU.Apply(tac) ->
    (handle_tactic ts tac, "Applied tactic.")

  | PU.Back ->
    begin match ts.ts_ps with
    | ActiveProof(_,back) -> 
      begin match pull back with
      | Left _ -> tacerror "Cannot backtrack"
      | Right(ps',pss) ->
        ({ ts with ts_ps = ActiveProof(ps',pss) }, "Backtracked to next alternative.")
      end
    | _ -> tacerror "last: no goals"
    end

  | PU.Last ->
    begin match ts.ts_ps with
    | ActiveProof(ps,back) -> 
      ({ ts with ts_ps = ActiveProof(CR.move_first_last ps,back) }, "Delayed current goal")
    | _ -> tacerror "last: no goals"
    end

  | PU.Admit ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_) -> 
      ({ts with ts_ps = ActiveProof(first (CR.apply_first CR.t_admit ps),mempty)}
      , "Admit goal.")
    | _ -> tacerror "admit: no goals"
    end

  | PU.PrintGoals(s) ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_back) -> 
      let msg = fsprintf "@[<v>Proof state %s:@\n%a@]" s pp_jus ps.CR.subgoals in
      (ts, msg)
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Theory closed.")
    end

  | PU.PrintProof ->
    begin match ts.ts_ps with
    | BeforeProof -> (ts, "No proof started yet.")
    | ActiveProof _ | ClosedTheory _ ->
      let pt =
        match ts.ts_ps with
        | BeforeProof -> assert false
        | ClosedTheory pt      -> pt
        | ActiveProof  (ps,_)  -> prove_by_admit ps
      in
      let pt = simplify_proof_tree  pt in
      let buf = Buffer.create 1024 in
      let fbuf = F.formatter_of_buffer buf in
      F.pp_set_margin fbuf 240;
      F.fprintf fbuf "%a" pp_proof_tree pt;
      (ts, Buffer.contents buf)
    end

  | PU.PrintGoal(s) ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_back) -> 
      let msg = fsprintf "Current goal in state %s:%a@."
        s
        pp_jus
        (Util.take 1 ps.CR.subgoals)
      in
      (ts, msg)
    | BeforeProof  -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Proof finished.")
    end

  | PU.Qed ->
    begin match ts.ts_ps with
    | ActiveProof(ps,_back) ->
      if ps.CR.subgoals = [] then
        ({ts with ts_ps = ClosedTheory (ps.CR.validation [])}, "Finished proof.")
      else
        tacerror "Cannot finish proof, open goals."
    | BeforeProof    -> (ts, "No proof started yet.")
    | ClosedTheory _ -> (ts, "Proof finished.")
    end

  | PU.Extract filename ->
    Extraction.extract ts filename;
    (ts, "EasyCrypt proof script extracted.")

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

