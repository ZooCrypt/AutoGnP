(*s Tactic engine: transformations of theory and proof states. *)

(*i*)
open CoreRules
open Rules
open Expr
open Type
open Util
open Syms
open Gsyms
open TheoryState
(*i*)

module Ht = Hashtbl
module PU = ParserUtil

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
  let g = get_proof_state ts in
  let apply_rule r ts = { ts with ts_ps = ActiveProof(t_first r g) } in
  let ju = match g.subgoals with
    | ju::_ -> ju
    | []    -> tacerror "cannot apply tactic: there is no goal"
  in
  match tac with
  | PU.Rnorm -> apply_rule Rules.t_norm ts

  | PU.Rnorm_nounfold ->
    apply_rule Rules.t_norm_nounfold ts

  | PU.Rnorm_unknown(is) ->
    let vmap = Game.vmap_of_globals ju.Game.ju_gdef in
    let vs = L.map (fun s -> mk_V (Ht.find vmap s)) is in
    apply_rule (Rules.t_norm_unknown vs) ts

  | PU.Rctxt_ev (sv,e,j) ->
    let ev = ju.Game.ju_ev in
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
    let vmap = Game.vmap_of_globals ju.Game.ju_gdef in
    let v1 = PU.create_var vmap sv ty in
    let e1 = PU.expr_of_parse_expr vmap ts e in
    let c = v1, e1 in
    apply_rule (t_ctxt_ev j c) ts

  | PU.Rcase_ev (e) ->
    let vmap = Game.vmap_of_globals ju.Game.ju_gdef in
    let e = PU.expr_of_parse_expr vmap ts e in
    apply_rule (t_case_ev e) ts

  | PU.Rindep -> apply_rule Rules.t_random_indep ts

  | PU.Rremove_ev(is) -> apply_rule (t_remove_ev is) ts

  | PU.Rsplit_ev(i) -> apply_rule (t_split_ev i) ts

  | PU.Rsimp ->
    tacerror "not implemented"
    (*i simp_event ts i*)
                             
  | PU.Rrewrite_ev(i,d) -> apply_rule (t_rw_ev i d) ts

  | PU.Rfalse_ev -> apply_rule t_false_ev ts

  | PU.Rswap(i,j) -> apply_rule (t_swap i j) ts

  | PU.Rswap_oracle(op,j) -> apply_rule (t_swap_oracle op j) ts

  | PU.Requiv(gd,ev) ->
    let vmap = Hashtbl.create 134 in
    let gd2 = PU.gdef_of_parse_gdef vmap ts gd in
    let ev = PU.expr_of_parse_expr vmap ts ev in
    let ju2 = { Game.ju_gdef = gd2; Game.ju_ev = ev } in
    apply_rule (t_conv true ju2) ts

  | PU.Rassm_dec(dir,s,xs) ->
    let assm = 
      try Ht.find ts.ts_assms_dec s 
      with Not_found -> tacerror "error no assumption %s" s in
    let needed = Assumption.needed_var dir assm in
    if L.length needed <> L.length xs then
      tacerror "Bad number of variables";
    let subst = 
      L.fold_left2
        (fun sigma v x -> 
          let v' = Vsym.mk x v.Vsym.ty in
          Vsym.M.add v v' sigma)
        Vsym.M.empty
        needed
        xs
    in
    apply_rule (Rules.t_assm_dec dir assm subst) ts

  | PU.Rassm_comp(s,ev_e) ->
    let assm = 
      try Ht.find ts.ts_assms_comp s 
      with Not_found -> tacerror "error no assumption %s" s
    in
    let vmap = Game.vmap_of_globals ju.Game.ju_gdef in
    let ev_e = PU.expr_of_parse_expr vmap ts ev_e in
    apply_rule (Rules.t_assm_comp assm ev_e) ts

  | PU.Rlet_abstract(i,sv,e) ->
    let vmap = Game.vmap_of_globals ju.Game.ju_gdef in
    let e = PU.expr_of_parse_expr vmap ts e in
    let v = PU.create_var vmap sv e.e_ty in
    apply_rule (Rules.t_let_abstract i v e) ts

  | PU.Rlet_unfold(i) ->
    apply_rule (Rules.t_let_unfold i) ts

  | PU.Rrnd(i,mctxt1,mctxt2) ->
    let (ty,rv) =
      match Game.get_ju_gcmd ju i with
      | Game.GSamp(v,_) -> (v.Vsym.ty, v)
      | _ -> tacerror "Line %i is not a sampling." i
    in
    let (v2,e2,forward) =
      match mctxt2 with
      | Some (sv2,e2) ->
        let vmap = Game.vmap_of_globals ju.Game.ju_gdef in
        (* bound name overshadows names in game *)
        let v2 = Vsym.mk sv2 ty in
        Hashtbl.add vmap sv2 v2;
        (v2,PU.expr_of_parse_expr vmap ts e2,0)
      | None ->
        (* field expressions containing the sampled variable *)
        let es = ref [] in
        let add_subterms e =
          L.iter
            (fun fe ->
               if Expr.Se.mem (mk_V rv) (Expr.e_vars fe) then es := !es @ [fe])
            (e_ty_outermost Type.mk_Fq e)
        in
        Game.iter_gdef_exp add_subterms ju.Game.ju_gdef;
        add_subterms ju.Game.ju_ev;
        (*i FIXME: it might be useful to refer to the ith expression using _i i*)
        match !es with
        | e::_ ->
          let rec aux j =
            if L.length ju.Game.ju_gdef <= i+j then (
              j - 1
            ) else (
              let gcmd = Game.get_ju_gcmd ju (i+j) in
              if Vsym.S.mem rv (Game.gcmd_all_vars gcmd)
              then j - 1
              else aux (j+1)
            )
          in
          let forward = aux 1 in
          (rv,e,forward)
        | []   -> tacerror "Sampled random variable does not occur in game."
    in
    let (v1,e1) =
      match mctxt1 with
      | Some(sv1,e1) ->
        let vmap = Game.vmap_of_globals ju.Game.ju_gdef in
        (* bound name overshadows names in game *)
        let v1 = Vsym.mk sv1 ty in
        Hashtbl.add vmap sv1 v1;
        let e1 = PU.expr_of_parse_expr vmap ts e1 in
        (v1,e1)
      | None when ty_equal ty mk_Fq ->
        Rules.invert_ctxt (v2,e2)
      | None ->
        tacerror "invert only implemented for Fq"
    in
    let ru_rand = t_random (i + forward) (v1,e1) (v2,e2) in
    F.printf ">>> forward %i\n" forward;
    let ru =
      if forward = 0 then ru_rand
      else ( t_swap i forward @. ru_rand @. t_norm @. t_swap (i+forward) (-forward))
    in
    apply_rule ru ts

  | PU.Rrnd_orcl((i,j,k) as op,mctxt1,sv2,e2) ->
    let ty =
      match Game.get_ju_lcmd ju (i,j,k) with
      | _,_,(_,Game.LSamp(v,_),_),_ -> v.Vsym.ty
      | _ -> tacerror "Position %i,%i,%i is not a sampling." i j k
    in
    let vmap = Game.vmap_in_orcl ju op in 
    let v2 = Vsym.mk sv2 ty in
    Hashtbl.add vmap sv2 v2;
    let e2 = PU.expr_of_parse_expr vmap ts e2 in
    let (v1,e1) = match mctxt1 with
      | Some(sv1,e1) ->
        let vmap = Game.vmap_in_orcl ju op in
        let v1 = Vsym.mk sv1 ty in
        Hashtbl.add vmap sv1 v1;
        let e1 = PU.expr_of_parse_expr vmap ts e1 in
        (v1,e1)
      | None when ty_equal ty mk_Fq ->
        Rules.invert_ctxt (v2,e2)
      | None ->
        tacerror "invert only implemented for Fq"
    in
    apply_rule (t_random_oracle (i,j,k) (v1,e1) (v2,e2)) ts

  | PU.Rbad(i,sx) ->
    let ty =
      match Game.get_ju_gcmd ju i with
      | Game.GLet(_,e') when is_H e' ->
        let _,e = destr_H e' in
        e.e_ty
      | _ -> tacerror "Line %is not hash assignment." i
    in
    let vx = PU.create_var (Game.vmap_of_globals ju.Game.ju_gdef) sx ty in
    apply_rule (t_bad i vx) ts

  | PU.Rexcept(i,es) ->
    let vmap = Game.vmap_of_globals ju.Game.ju_gdef in
    let es = L.map (PU.expr_of_parse_expr vmap ts) es in
    apply_rule (t_except i es) ts

  | PU.Rexcept_orcl(_op,_es) ->
    failwith "undefined"
    (*i
    let es = L.map (PU.expr_of_parse_expr ts) es in
    apply_rule (t_except_oracle op es) ts
    i*)
   
  | PU.Rrewrite_orcl(op,dir) ->
    apply_rule (t_rewrite_oracle op dir) ts

  | PU.Radd_test(op,t,aname,fvs) ->
    let _, juoc = Game.get_ju_octxt ju op in
    let vmap = Game.vmap_in_orcl ju op in
    let t = PU.expr_of_parse_expr vmap ts t in
    let oty = juoc.Game.juoc_osym.Osym.dom in
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
    apply_rule (t_add_test op t asym fvs) ts
  
let pp_jus fmt jus =  
  match jus with
  | [] -> F.printf "No remaining goals, proof completed.@\n"
  | jus ->
    let pp_goal i ju =
      F.fprintf fmt "goal %i:@\n%a@\n@\n" (i + 1) Game.pp_ju ju in
    L.iteri pp_goal jus 


let handle_instr ts instr =
  match instr with
  | PU.RODecl(s,ro,t1,t2) ->
    if Ht.mem ts.ts_rodecls s then
      tacerror "Random oracle with same name already declared.";
    Ht.add ts.ts_rodecls s
      (Hsym.mk s ro (PU.ty_of_parse_ty ts t1) (PU.ty_of_parse_ty ts t2));
    (ts, "Declared random oracle")

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
    let vmap, sigma = Game.merge_vmap vmap1 vmap2 in
    let g1 = Game.subst_v_gdef sigma g1 in
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
    ({ ts with ts_ps = ActiveProof(t_id ju) }, "Started proof of judgment.")

  | PU.Apply(tac) ->
    (handle_tactic ts tac, "Applied tactic.")

  | PU.Last ->
    begin match ts.ts_ps with
    | ActiveProof (g) -> 
      ({ ts with ts_ps = ActiveProof(t_first_last g) }, "Delayed current goal")
    | _ -> tacerror "last: no goals"
    end

  | PU.Admit ->
    begin match ts.ts_ps with
    | ActiveProof(g) -> 
      ({ts with ts_ps = ActiveProof(t_first t_admit g)}, "Admit goal.")
    | _ -> tacerror "admit: no goals"
    end

  | PU.PrintGoals(s) ->
    begin match ts.ts_ps with
    | ActiveProof(g) -> 
      let msg = fsprintf "@[<v>Proof state %s:@\n%a@." s pp_jus g.subgoals in
      (ts, msg)
    | BeforeProof -> (ts, "No proof started yet.")
    | ClosedTheory -> (ts, "Theory closed.")
    end

  | PU.PrintGoal(s) ->
    begin match ts.ts_ps with
    | ActiveProof(g) -> 
      let msg = fsprintf "@[<v>Current goal in state %s:@\n%a@."
        s
        pp_jus
        (Util.take 1 g.subgoals)
      in
      (ts, msg)
    | BeforeProof  -> (ts, "No proof started yet.")
    | ClosedTheory -> (ts, "Proof finished.")
    end

  (*i FIXME: add qed/save tactic that changes proof_state to ClosedTheory if no goal remains i*)
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

