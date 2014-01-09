(** Tactic engine: transformations of proof states. *)
open CoreRules
open ParserUtil
open Rules
open Expr
open Type
open Util
open TheoryState

module Ht = Hashtbl
module F  = Format

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
  let g =
    match ts.ts_ps with
    | ActiveProof g -> g
    | BeforeProof   -> tacerror "cannot apply tactic: no active proof"
    | ClosedTheory  -> tacerror "cannot apply tactic: theory closed"
  in
  let apply_rule r ts = { ts with ts_ps = ActiveProof(t_first r g) } in
  let ju = match g.subgoals with
    | ju::_ -> ju
    | [] -> tacerror "cannot apply tactic: there is no goal"
  in
  match tac with
  | Rnorm -> apply_rule t_norm ts

  | Rnorm_nounfold ->
    apply_rule t_norm_nounfold ts

  | Rnorm_unknown(is) ->
    let vs = List.map (fun s -> mk_V (Ht.find ts.ts_vars s)) is in
    apply_rule (t_norm_unknown vs) ts

  | Rctxt_ev (sv,e,j) ->
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
    let e1 = expr_of_parse_expr ts e in
    let c = v1, e1 in
    apply_rule (t_ctxt_ev j c) ts

  | Rindep -> apply_rule t_random_indep ts

  | Rswap(i,j) -> apply_rule (t_swap i j) ts

  | Rswap_oracle(op,j) -> apply_rule (t_swap_oracle op j) ts

  | Requiv(gd,ev) ->
    let gd = gdef_of_parse_gdef true ts gd in 
      (* reuse variables from previous games *)
    let ev = 
      match ev with
      | None -> ju.Game.ju_ev
      | Some e -> expr_of_parse_expr ts e in
    apply_rule (t_conv true { Game.ju_gdef = gd; Game.ju_ev = ev }) ts

  | Rassm(dir,s,xs) ->
    let assm = 
      try Ht.find ts.ts_assms s 
      with Not_found -> tacerror "error no assumption %s" s in
    let needed = Assumption.needed_var dir assm in
    if List.length needed <> List.length xs then
      tacerror "Bad number of variables";
    let subst = 
      List.fold_left2 (fun s v x -> 
        let v' = create_var_reuse ts x v.Vsym.ty in
        Vsym.M.add v v' s) Vsym.M.empty needed xs in
    apply_rule (Rules.t_assm dir assm subst) ts

  | Rlet_abstract(i,sv,e) ->
    let e = expr_of_parse_expr ts e in
    let v = create_var false ts sv e.e_ty in
    apply_rule (t_let_abstract i v e) ts

  | Rlet_unfold(i) ->
    apply_rule (t_let_unfold i) ts

  | Rrandom(i,mctxt1,sv2,e2,svlet) ->
    let ty =
      match Game.get_ju_gcmd ju i with
      | Game.GSamp(v,_) -> v.Vsym.ty
      | _ -> tacerror "Line %i is not a sampling." i
    in
    let ts' = ts_copy ts in
    let v2 = create_var false ts' sv2 ty in
    let e2 = expr_of_parse_expr ts' e2 in
    let (v1,e1) =
      match mctxt1 with
      | Some(sv1,e1) ->
        let ts' = ts_copy ts in
        let v1 = create_var false ts' sv1 ty in
        let e1 = expr_of_parse_expr ts' e1 in
        (v1,e1)
      | None when ty_equal ty mk_Fq ->
        invert_ctxt (v2,e2)
      | None ->
        tacerror "invert only implemented for Fq"
    in
    let vlet = create_var false ts svlet ty in
    apply_rule (t_random i (v1,e1) (v2,e2) vlet) ts

  | Rrandom_oracle((i,j,k),mctxt1,sv2,e2,svlet) ->
    let ty =
      match Game.get_ju_lcmd ju (i,j,k) with
      | _,_,(_,Game.LSamp(v,_),_),_ -> v.Vsym.ty
      | _ -> tacerror "Position %i,%i,%i is not a sampling." i j k
    in
    let ts' = ts_copy ts in
    let v2 = create_var false ts' sv2 ty in
    let e2 = expr_of_parse_expr ts' e2 in
    let (v1,e1) = match mctxt1 with
      | Some(sv1,e1) ->
        let ts' = ts_copy ts in
        let v1 = create_var false ts' sv1 ty in
        let e1 = expr_of_parse_expr ts' e1 in
        (v1,e1)
      | None when ty_equal ty mk_Fq ->
        invert_ctxt (v2,e2)
      | None ->
        tacerror "invert only implemented for Fq"
    in
    let vlet = create_var false ts svlet ty in
    apply_rule (t_random_oracle (i,j,k) (v1,e1) (v2,e2) vlet) ts

  | Rbad(i,sx) ->
    let ty =
      match Game.get_ju_gcmd ju i with
      | Game.GLet(_,e') when is_H e' ->
        let _,e = destr_H e' in
        e.e_ty
      | _ -> tacerror "Line %is not hash assignment." i
    in
    let vx = create_var false ts sx ty in
    apply_rule (t_bad i vx) ts

  | Rexcept(i,es) ->
    let es = List.map (expr_of_parse_expr ts) es in
    apply_rule (t_except i es) ts

  | Rexcept_oracle(op,es) ->
    let es = List.map (expr_of_parse_expr ts) es in
    apply_rule (t_except_oracle op es) ts
   
  | Rrewrite_oracle(op,dir) ->
    apply_rule (t_rewrite_oracle op dir) ts

  | Radd_test(op,t,aname,fvs) ->
    let t = expr_of_parse_expr ts t in
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
  | [] -> Format.printf "No remaining goals, proof completed.@\n"
  | jus ->
    let pp_goal i ju =
      Format.fprintf fmt "goal %i:@\n%a@\n@\n" (i + 1) Game.pp_ju ju in
    List.iteri pp_goal jus 

let handle_instr ts instr =
  let ts = ts_copy ts in
  (* FIXME: only allow declarations in BeforeProof state *)
  match instr with
  | RODecl(s,t1,t2) ->
    if Ht.mem ts.ts_rodecls s then
      tacerror "Random oracle with same name already declared.";
    Ht.add ts.ts_rodecls s
      (Hsym.mk s (ty_of_parse_ty ts t1) (ty_of_parse_ty ts t2));
    (ts, "Declared random oracle")

  | EMDecl(s,g1,g2,g3) ->
    if Ht.mem ts.ts_emdecls s then
      tacerror "Bilinear map with same name already declared.";
    Ht.add ts.ts_emdecls s
      (Esym.mk s (create_groupvar ts g1) (create_groupvar ts g2) (create_groupvar ts g3));
    (ts, "Declared bilinear map.")

  | ODecl(s,t1,t2) ->
      if Ht.mem ts.ts_odecls s then 
        tacerror "Oracle with same name already declared.";
    Ht.add ts.ts_odecls s 
      (Osym.mk s (ty_of_parse_ty ts t1) (ty_of_parse_ty ts t2));
    (ts, "Declared oracle.")

  | ADecl(s,t1,t2) ->
    if Ht.mem ts.ts_adecls s then 
      tacerror "adversary with same name already declared.";
    Ht.add ts.ts_adecls s 
      (Asym.mk s (ty_of_parse_ty ts t1) (ty_of_parse_ty ts t2));
    (ts, "Declared adversary.")

  | AssmDec(s,g0,g1,priv) ->
    let ts' = ts_resetvars ts in
    let g0 = gdef_of_parse_gdef true ts' g0 in
    let g1 = gdef_of_parse_gdef true ts' g1 in
    let priv = List.fold_left (fun s x -> 
      try Vsym.S.add (Ht.find ts'.ts_vars x) s
      with Not_found -> tacerror "unknown variable %s" x)
      Vsym.S.empty priv in
    if Ht.mem ts.ts_assms s then
      tacerror "assumption with the same name already exists";
    Ht.add ts.ts_assms s (Assumption.mk_ad g0 g1 priv);
    (ts, "Declared assumption.")
    
  | Judgment(gd, e) ->
    let ts = ts_resetvars ts in
    let ju = ju_of_parse_ju false ts gd e in
    ({ ts with ts_ps = ActiveProof(t_id ju) }, "Started proof of judgment.")

  | Apply(tac) -> (handle_tactic ts tac, "Applied tactic.")

  | Last ->
    begin match ts.ts_ps with
    | ActiveProof (g) -> 
      ({ ts with ts_ps = ActiveProof(t_first_last g) }, "Delayed current goal")
    | _ -> tacerror "last: no goals"
    end

  | Admit ->
    begin match ts.ts_ps with
    | ActiveProof(g) -> 
      ({ts with ts_ps = ActiveProof(t_first t_admit g)}, "Admit goal.")
    | _ -> tacerror "admit: no goals"
    end

  | PrintGoals(s) ->
    begin match ts.ts_ps with
    | ActiveProof(g) -> 
      let msg = fsprintf "@[<v>Proof state %s:@\n%a@." s pp_jus g.subgoals |> fsget in
      (ts, msg)
    | BeforeProof -> (ts, "No proof started yet.")
    | ClosedTheory -> (ts, "Theory closed.")
    end

  | PrintGoal(s) ->
    begin match ts.ts_ps with
    | ActiveProof(g) -> 
      let msg = fsprintf "@[<v>Current goal in state %s:@\n%a@."
        s
        pp_jus
        (Util.take 1 g.subgoals)
    |> fsget
      in
      (ts, msg)
    | BeforeProof -> (ts, "No proof started yet.")
    | ClosedTheory -> (ts, "Proof finished.")
    end
(* FIXME: add qed/save tactic that changes proof_state to ClosedTheory if no goal remains *)
  | Extract filename ->
    Extract.extract ps filename;
    (ps, "file extracted")

let eval_theory s =
  let pt = Parse.theory s in
  List.fold_left (fun ps i ->
                    let (ps', s) = handle_instr ps i in
                    print_endline s;
                    ps')
    (mk_ts ())
    pt
