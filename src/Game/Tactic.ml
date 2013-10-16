open ParserUtil


let handle_tactic ps tac jus = 
  match tac with
  | Rnorm ->
      { ps with ps_goals = Some(CoreRule.apply Rules.rnorm jus) }

  | Rrandom(i,sv1,e1,sv2,e2) ->
      let ty =
        (match ps.ps_goals with
         | Some(ju::_) ->
             (match Game.get_ju_gcmd ju i with
              | Game.GSamp(v,_) -> v.Vsym.ty
              | _ -> assert false)
         | _ -> assert false)
      in
      let v1 = create_var ps sv1 ty in
      let e1 = expr_of_parse_expr ps.ps_vars e1 in
      Ht.remove ps.ps_vars sv1;
      let v2 = create_var ps sv2 ty in
      let e2 = expr_of_parse_expr ps.ps_vars e2 in
      Ht.remove ps.ps_vars sv2;
      { ps with ps_goals = Some(CoreRule.apply (CoreRule.rrandom i (v1,e1) (v2,e2)) jus) }

  | Rrandom_oracle(i,j,k,sv1,e1,sv2,e2) ->
      let ty =
        (match ps.ps_goals with
         | Some(ju::_) ->
             (match Game.get_ju_lcmd ju (i,j,k) with
              | _,_,(_,Game.LSamp(v,_),_),_ -> v.Vsym.ty
              | _ -> assert false)
         | _ -> assert false)
      in
      let v1 = create_var ps sv1 ty in
      let e1 = expr_of_parse_expr ps.ps_vars e1 in
      Ht.remove ps.ps_vars sv1;
      let v2 = create_var ps sv2 ty in
      let e2 = expr_of_parse_expr ps.ps_vars e2 in
      Ht.remove ps.ps_vars sv2;
      { ps with ps_goals = Some(CoreRule.apply
                                 (CoreRule.rrandom_oracle (i,j,k) (v1,e1) (v2,e2))
                                 jus) }

let handle_instr ps instr =
  match instr with
  | Apply(tac) ->
      (match ps.ps_goals with
       | Some(jus) ->
           handle_tactic ps tac jus
       | None -> assert false)
  | PrintGoals(s) ->
      Format.printf "proof state %s:\n" s;
      (match ps.ps_goals with
       | Some(jus) ->
           let i = ref 0 in
           List.iter (fun ju -> incr i; Format.printf "goal %i:\n%a\n\n" !i Game.pp_ju ju) jus;
       | None -> Format.printf "No goals\n\n%!");
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
      let ju = ju_of_parse_ju ps gd e in
      { ps with ps_goals = Some([ju]) }

let eval_theory s =
  let pt = Parse.theory s in
  List.fold_left (fun ps i -> handle_instr ps i) mk_ps pt