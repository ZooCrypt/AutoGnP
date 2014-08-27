(** Tactic engine: transformations of proof states. *)
open CoreRules
open Expr
open Type
open Util
open TheoryState

module Ht = Hashtbl
module PU = ParserUtil

let fail_unless c s =
  if not (c ()) then tacerror s

let create_var reuse ts s ty =
  match TheoryState.create_var reuse ts s ty with
  | None -> tacerror "Variable %s already defined" s
  | Some v -> v

let invert_ctxt (v,e) =
  let hole_occurs p =
    List.exists
      (fun (_,m) ->
         List.exists (fun (e,_) -> Se.mem (mk_V v) (e_vars e)) m)
      p
  in
  match Poly.polys_of_field_expr (CAS.norm (fun x -> x) e) with
  | (nom, None) ->
    (* v = v' * g + h => v' = (v - h) / g *)
    let (g,h) = Poly.factor_out (mk_V v) nom in
    let e' = mk_FDiv (mk_FMinus (mk_V v) (Poly.exp_of_poly h))
                     (Poly.exp_of_poly g)
    in (v, e' |> Norm.norm_expr |> Norm.abbrev_ggen)
  | (nom, Some(denom)) when not (hole_occurs denom) ->
    (* v = (v' * g + h) / denom => v' = (v * denom - h) / g *)
    let (g,h) = Poly.factor_out (mk_V v) nom in
    let e' = mk_FDiv
               (mk_FMinus (mk_FMult [mk_V v; Poly.exp_of_poly denom]) (Poly.exp_of_poly h))
               (Poly.exp_of_poly g)
    in (v, e' |> Norm.norm_expr |> Norm.abbrev_ggen)
  | (_nom, Some(_denom)) ->
    tacerror
      "invert does not support denominators with hole-occurences in contexts"

let handle_tactic ts tac =
  let g = get_proof_state ts in
  let apply_rule r ts = { ts with ts_ps = ActiveProof(t_first r g) } in
  let ju = match g.subgoals with
    | ju::_ -> ju
    | [] -> tacerror "cannot apply tactic: there is no goal"
  in
  (* FIXME: for now, we just clean up ts_vars here *)
  let ts = ts_importvars ts ju in
  match tac with
  | PU.Rnorm -> apply_rule Rules.t_norm ts

  | PU.Rnorm_nounfold ->
    apply_rule Rules.t_norm_nounfold ts

  | PU.Rnorm_unknown(is) ->
    let vs = List.map (fun s -> mk_V (Ht.find ts.ts_vars s)) is in
    apply_rule (Rules.t_norm_unknown vs) ts

  | PU.Rctxt_ev (sv,e,j) ->
    (* TODO: how to be in the good typing context *)
    let ev = ju.Game.ju_ev in
    let b =
      match ev.e_node with
      | Nary(Land,es) when j < List.length es ->
        List.nth es j
      | _ when j = 0 -> ev
      | _ -> tacerror "rctxt_ev: bad index"
    in
    let ty = 
      if is_Eq b then (fst (destr_Eq b)).e_ty
      else if is_Exists b then
        let (e1,_,_) = destr_Exists b in e1.e_ty 
      else tacerror "rctxt_ev: bad event"
    in
    let v1 = create_var false ts sv ty in
    let e1 = PU.expr_of_parse_expr ts e in
    let c = v1, e1 in
    apply_rule (t_ctxt_ev j c) ts

  | PU.Rcase_ev (e) ->
    let e = PU.expr_of_parse_expr ts e in
    apply_rule (t_case_ev e) ts

  | PU.Rindep -> apply_rule Rules.t_random_indep ts

  | PU.Rremove_ev(is) -> apply_rule (t_remove_ev is) ts

  | PU.Rsplit_ev(i) -> apply_rule (t_split_ev i) ts

  | PU.Rrewrite_ev(i,d) -> apply_rule (t_rw_ev i d) ts

  | PU.Rfalse_ev -> apply_rule t_false_ev ts

  | PU.Rswap(i,j) -> apply_rule (t_swap i j) ts

  | PU.Rswap_oracle(op,j) -> apply_rule (t_swap_oracle op j) ts

  | PU.Requiv(gd,ev) ->
    let gd = PU.gdef_of_parse_gdef true ts gd in 
    (* reuse variables from previous games *)
    let ev = 
      match ev with
      | None -> ju.Game.ju_ev
      | Some e -> PU.expr_of_parse_expr ts e
    in
    apply_rule (t_conv true { Game.ju_gdef = gd; Game.ju_ev = ev }) ts

  | PU.Rassm_decisional(dir,s,xs) ->
    let assm = 
      try Ht.find ts.ts_assms_dec s 
      with Not_found -> tacerror "error no assumption %s" s in
    let needed = Assumption.needed_var dir assm in
    if List.length needed <> List.length xs then
      tacerror "Bad number of variables";
    let subst = 
      List.fold_left2 (fun s v x -> 
        let v' = create_var_reuse ts x v.Vsym.ty in
        Vsym.M.add v v' s) Vsym.M.empty needed xs in
    apply_rule (Rules.t_assm_decisional dir assm subst) ts

  | PU.Rassm_computational(s,ev_e) ->
    let assm = 
      try Ht.find ts.ts_assms_comp s 
      with Not_found -> tacerror "error no assumption %s" s
    in
    let ev_e = PU.expr_of_parse_expr ts ev_e in
    apply_rule (Rules.t_assm_computational assm ev_e) ts

  | PU.Rlet_abstract(i,sv,e) ->
    let e = PU.expr_of_parse_expr ts e in
    let v = create_var false ts sv e.e_ty in
    apply_rule (Rules.t_let_abstract i v e) ts

  | PU.Rlet_unfold(i) ->
    apply_rule (Rules.t_let_unfold i) ts

  | PU.Rrandom(i,mctxt1,mctxt2,svlet) ->
    let (ty,rv) =
      match Game.get_ju_gcmd ju i with
      | Game.GSamp(v,_) -> (v.Vsym.ty, v)
      | _ -> tacerror "Line %i is not a sampling." i
    in
    let ts' = ts_copy ts in
    let (v2,e2) =
      match mctxt2 with
      | Some (sv2,e2) ->
        let v2 = create_var false ts' sv2 ty in
        (v2,PU.expr_of_parse_expr ts' e2)
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
        (* FIXME: it might be useful to refer to the ith expression using _i *)
        match !es with
        | e::_ -> (rv,e)
        | []   -> tacerror "Sampled random variable does not occur in game."
    in
    let (v1,e1) =
      match mctxt1 with
      | Some(sv1,e1) ->
        let ts' = ts_copy ts in
        let v1 = create_var false ts' sv1 ty in
        let e1 = PU.expr_of_parse_expr ts' e1 in
        (v1,e1)
      | None when ty_equal ty mk_Fq ->
        invert_ctxt (v2,e2)
      | None ->
        tacerror "invert only implemented for Fq"
    in
    let vlet = create_var false ts svlet ty in
    apply_rule (t_random i (v1,e1) (v2,e2) vlet) ts

  | PU.Rrandom_oracle((i,j,k),mctxt1,sv2,e2,svlet) ->
    let ty =
      match Game.get_ju_lcmd ju (i,j,k) with
      | _,_,(_,Game.LSamp(v,_),_),_ -> v.Vsym.ty
      | _ -> tacerror "Position %i,%i,%i is not a sampling." i j k
    in
    let ts' = ts_copy ts in
    let v2 = create_var false ts' sv2 ty in
    let e2 = PU.expr_of_parse_expr ts' e2 in
    let (v1,e1) = match mctxt1 with
      | Some(sv1,e1) ->
        let ts' = ts_copy ts in
        let v1 = create_var false ts' sv1 ty in
        let e1 = PU.expr_of_parse_expr ts' e1 in
        (v1,e1)
      | None when ty_equal ty mk_Fq ->
        invert_ctxt (v2,e2)
      | None ->
        tacerror "invert only implemented for Fq"
    in
    let vlet = create_var false ts svlet ty in
    apply_rule (t_random_oracle (i,j,k) (v1,e1) (v2,e2) vlet) ts

  | PU.Rbad(i,sx) ->
    let ty =
      match Game.get_ju_gcmd ju i with
      | Game.GLet(_,e') when is_H e' ->
        let _,e = destr_H e' in
        e.e_ty
      | _ -> tacerror "Line %is not hash assignment." i
    in
    let vx = create_var false ts sx ty in
    apply_rule (t_bad i vx) ts

  | PU.Rexcept(i,es) ->
    let es = List.map (PU.expr_of_parse_expr ts) es in
    apply_rule (t_except i es) ts

  | PU.Rexcept_oracle(op,es) ->
    let es = List.map (PU.expr_of_parse_expr ts) es in
    apply_rule (t_except_oracle op es) ts
   
  | PU.Rrewrite_oracle(op,dir) ->
    apply_rule (t_rewrite_oracle op dir) ts

  | PU.Radd_test(op,t,aname,fvs) ->
    let t = PU.expr_of_parse_expr ts t in
    let _, juoc = Game.get_ju_octxt ju op in
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
    fail_unless (fun () -> List.length fvs = List.length tys)
      "number of given variables does not match type";
    let fvs = List.map2 (fun v ty -> create_var false ts v ty) fvs tys in
    apply_rule (t_add_test op t asym fvs) ts
  
let pp_jus fmt jus =  
  match jus with
  | [] -> F.printf "No remaining goals, proof completed.@\n"
  | jus ->
    let pp_goal i ju =
      F.fprintf fmt "goal %i:@\n%a@\n@\n" (i + 1) Game.pp_ju ju in
    List.iteri pp_goal jus 

let handle_instr ts instr =
  let ts = ts_copy ts in
  (* FIXME: only allow declarations in BeforeProof state *)
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
    let ts' = ts_resetvars ts in
    let g0 = PU.gdef_of_parse_gdef true ts' g0 in
    let g1 = PU.gdef_of_parse_gdef true ts' g1 in
    let priv = List.fold_left (fun s x -> 
      try Vsym.S.add (Ht.find ts'.ts_vars x) s
      with Not_found -> tacerror "unknown variable %s" x)
      Vsym.S.empty priv in
    if Ht.mem ts.ts_assms_dec s then
      tacerror "assumption with the same name already exists";
    Ht.add ts.ts_assms_dec s (Assumption.mk_ad s g0 g1 priv);
    (ts, "Declared decisional assumption.")

  | PU.AssmComp(s,g,ev_var,ev_ty,ev,priv) ->
    let ts' = ts_resetvars ts in
    let g = PU.gdef_of_parse_gdef true ts' g in
    let priv = List.fold_left (fun s x -> 
      try Vsym.S.add (Ht.find ts'.ts_vars x) s
      with Not_found -> tacerror "unknown variable %s" x)
      Vsym.S.empty priv
    in
    let ev_ty  = PU.ty_of_parse_ty ts' ev_ty in
    let ev_var = create_var false ts' ev_var ev_ty in
    let ev = PU.expr_of_parse_expr ts' ev in
    let assm = Assumption.mk_ac s g ev_var ev priv in
    if Ht.mem ts.ts_assms_comp s then
      tacerror "assumption with the same name already exists";
    Ht.add ts.ts_assms_comp s assm;
    (ts, "Declared computational assumption.")
    
  | PU.Judgment(gd, e) ->
    let ts = ts_resetvars ts in
    let ju = PU.ju_of_parse_ju false ts gd e in
    ({ ts with ts_ps = ActiveProof(t_id ju) }, "Started proof of judgment.")

  | PU.Apply(tac) -> (handle_tactic ts tac, "Applied tactic.")

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
    | BeforeProof -> (ts, "No proof started yet.")
    | ClosedTheory -> (ts, "Proof finished.")
    end
(* FIXME: add qed/save tactic that changes proof_state to ClosedTheory if no goal remains *)
  | PU.Extract filename ->
    Extraction.extract ts filename;
    (ts, "file extracted")

let eval_theory s =
  let pt = Parse.theory s in
  List.fold_left (fun ps i ->
                    let (ps', s) = handle_instr ps i in
                    print_endline s;
                    ps')
    (mk_ts ())
    pt
