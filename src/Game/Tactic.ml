open ParserUtil
open CoreRule
open Rules

module Ht = Hashtbl

let handle_tactic ps tac jus =
  let apply_rule r ps = { ps with ps_goals = Some(apply r jus) } in
  match tac with
  | Rnorm -> apply_rule rnorm ps

  | Rnorm_unknown(is) ->
      let vs = List.map (fun s -> Expr.mk_V (Ht.find ps.ps_vars s)) is in
      apply_rule (rnorm_unknown vs) ps

  | Rindep -> apply_rule rrandom_indep ps

  | Rswap(i,j) -> apply_rule (rswap i j) ps

  | Requiv(gd) ->
      let gd = gdef_of_parse_gdef true ps gd in (* reuse variables from previous games *)
      let ju = (match jus with
                | ju::_ -> ju
                | _ -> assert false)
      in
      apply_rule (rconv { Game.ju_gdef = gd; Game.ju_ev = ju.Game.ju_ev }) ps

  | Rbddh(s) ->
      let v = create_var false ps s Type.mk_Fq in
      apply_rule (rbddh v) ps

  | Rddh(s) ->
      let v = create_var false ps s Type.mk_Fq in
      apply_rule (rddh v) ps

  | Rlet_abstract(i,sv,e) ->
      let e = expr_of_parse_expr ps.ps_vars e in
      let v = create_var false ps sv e.Expr.e_ty in
      apply_rule (rlet_abstract i v e) ps

  | Rrandom(i,sv1,e1,sv2,e2) ->
      let ty =
        (match ps.ps_goals with
         | Some(ju::_) ->
             (match Game.get_ju_gcmd ju i with
              | Game.GSamp(v,_) -> v.Vsym.ty
              | _ -> assert false)
         | _ -> assert false)
      in
      let v1 = create_var false ps sv1 ty in
      let e1 = expr_of_parse_expr ps.ps_vars e1 in
      Ht.remove ps.ps_vars sv1;
      let v2 = create_var false ps sv2 ty in
      let e2 = expr_of_parse_expr ps.ps_vars e2 in
      Ht.remove ps.ps_vars sv2;
      apply_rule (rrandom i (v1,e1) (v2,e2)) ps

  | Rrandom_oracle(i,j,k,sv1,e1,sv2,e2) ->
      let ty =
        (match ps.ps_goals with
         | Some(ju::_) ->
             (match Game.get_ju_lcmd ju (i,j,k) with
              | _,_,(_,Game.LSamp(v,_),_),_ -> v.Vsym.ty
              | _ -> assert false)
         | _ -> assert false)
      in
      let v1 = create_var false ps sv1 ty in
      let e1 = expr_of_parse_expr ps.ps_vars e1 in
      Ht.remove ps.ps_vars sv1;
      let v2 = create_var false ps sv2 ty in
      let e2 = expr_of_parse_expr ps.ps_vars e2 in
      Ht.remove ps.ps_vars sv2;
      apply_rule (rrandom_oracle (i,j,k) (v1,e1) (v2,e2)) ps

let pp_goals fmt gs = 
  match gs with
  | None -> Format.printf "No goals@\n"
  | Some [] -> Format.printf "No remaining goals, proof completed.@\n"
  | Some jus ->
    let pp_goal i ju =
      Format.fprintf fmt "goal %i:@\n%a@\n@\n" i Game.pp_ju ju in
    List.iteri pp_goal jus 
      

let handle_instr ps instr =
  match instr with
  | Apply(tac) ->
      (match ps.ps_goals with
       | Some(jus) ->
           handle_tactic ps tac jus
       | None -> assert false)
  | PrintGoals(s) ->
      Format.printf "@[<v>proof state %s:@\n%a@." s pp_goals ps.ps_goals;
      ps
  | ODecl(s,t1,t2) ->
      if Ht.mem ps.ps_odecls s then failwith "oracle with same name already declared."
      else Ht.add ps.ps_odecls s (Osym.mk s (ty_of_parse_ty t1) (ty_of_parse_ty t2));
      ps
  | ADecl(s,t1,t2) ->
      if Ht.mem ps.ps_adecls s then failwith "adversary with same name already declared."
      else Ht.add ps.ps_adecls s (Asym.mk s (ty_of_parse_ty t1) (ty_of_parse_ty t2));
      ps
  | Judgment(gd, e) ->
      let ju = ju_of_parse_ju false ps gd e in
      { ps with ps_goals = Some([ju]) }

let eval_theory s =
  let pt = Parse.theory s in
  List.fold_left (fun ps i -> handle_instr ps i) (mk_ps ()) pt
