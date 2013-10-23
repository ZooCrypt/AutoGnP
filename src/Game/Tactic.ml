open Inv
open ParserUtil
open CoreRule
open Rules
open Expr
open Type
open Util

module Ht = Hashtbl

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
    failwith "invert does not support denominators with hole-occurences in contexts"

let handle_tactic ps tac jus =
  let apply_rule r ps = { ps with ps_goals = Some(apply r jus) } in
  let ju = match jus with
    | ju::_ -> ju
    | [] -> failwith "cannot apply tactic: there is no goal"
  in
  match tac with
  | Rnorm -> apply_rule rnorm ps

  | Rnorm_nounfold ->
    apply_rule rnorm_nounfold ps

  | Rnorm_unknown(is) ->
    let vs = List.map (fun s -> mk_V (Ht.find ps.ps_vars s)) is in
    apply_rule (rnorm_unknown vs) ps

  | Rctxt_ev (sv,e) ->
    let ev = ju.Game.ju_ev in
    let ty = 
      if Expr.is_Eq ev then (fst (Expr.destr_Eq ev)).Expr.e_ty
      else if Expr.is_ElemH ev then
        let (e1,_,_) = Expr.destr_ElemH ev in e1.Expr.e_ty 
      else failwith "rctxt_ev: bad event" in
    let v1 = create_var false ps sv ty in
    let e1 = expr_of_parse_expr ps e in
    let c = v1, e1 in
    let ev = 
      if Expr.is_Eq ev then
        let (e1,e2) = Expr.destr_Eq ev in
        Expr.mk_Eq (Expr.inst_ctxt c e1) (Expr.inst_ctxt c e2) 
      else if Expr.is_ElemH ev then
        let (e1,e2,h) = Expr.destr_ElemH ev in
        Expr.mk_ElemH (Expr.inst_ctxt c e1) (Expr.inst_ctxt c e2) h 
      else failwith "rctxt_ev: bad event"
    in
    apply_rule (rctxt_ev ev c) ps

  | Rindep -> apply_rule rrandom_indep ps

  | Rswap(i,j) -> apply_rule (rswap i j) ps

  | Requiv(gd,ev) ->
    let gd = gdef_of_parse_gdef true ps gd in 
      (* reuse variables from previous games *)
    let ev = 
      match ev with
      | None -> ju.Game.ju_ev
      | Some e -> expr_of_parse_expr ps e in
    apply_rule (rconv { Game.ju_gdef = gd; Game.ju_ev = ev }) ps

  | Rassm(dir,s,xs) ->
    let assm = 
      try Ht.find ps.ps_assm s 
      with Not_found -> failwith ("error no assumption "^s) in
    let needed = Assumption.needed_var dir assm in
    if List.length needed <> List.length xs then
      failwith "Bad number of variables";
    let subst = 
      List.fold_left2 (fun s v x -> 
        let v' = create_var true ps x v.Vsym.ty in
        Vsym.M.add v v' s) Vsym.M.empty needed xs in
    apply_rule (Rules.rassm dir assm subst) ps

  | Rlet_abstract(i,sv,e) ->
    let e = expr_of_parse_expr ps e in
    let v = create_var false ps sv e.e_ty in
    apply_rule (rlet_abstract i v e) ps

  | Rlet_unfold(i) ->
    apply_rule (rlet_unfold i) ps

  | Rrandom(i,mctxt1,sv2,e2,svlet) ->
    let ty =
      match Game.get_ju_gcmd ju i with
      | Game.GSamp(v,_) -> v.Vsym.ty
      | _ -> assert false
    in
    let v2 = create_var false ps sv2 ty in
    let e2 = expr_of_parse_expr ps e2 in
    Ht.remove ps.ps_vars sv2;
    let (v1,e1) = match mctxt1 with
      | Some(sv1,e1) ->
        let v1 = create_var false ps sv1 ty in
        let e1 = expr_of_parse_expr ps e1 in
        Ht.remove ps.ps_vars sv1;
        (v1,e1)
      | None when ty_equal ty mk_Fq ->
        invert_ctxt (v2,e2)
      | None ->
        failwith "invert only implemented for Fq"
    in
    let vlet = create_var false ps svlet ty in
    apply_rule (rrandom i (v1,e1) (v2,e2) vlet) ps

  | Rrandom_oracle((i,j,k),mctxt1,sv2,e2,svlet) ->
    let ty =
      match Game.get_ju_lcmd ju (i,j,k) with
      | _,_,(_,Game.LSamp(v,_),_),_ -> v.Vsym.ty
      | _ -> assert false
    in
    let v2 = create_var false ps sv2 ty in
    let e2 = expr_of_parse_expr ps e2 in
    Ht.remove ps.ps_vars sv2;
    let (v1,e1) = match mctxt1 with
      | Some(sv1,e1) ->
        let v1 = create_var false ps sv1 ty in
        let e1 = expr_of_parse_expr ps e1 in
        Ht.remove ps.ps_vars sv1;
        (v1,e1)
      | None when ty_equal ty mk_Fq ->
        invert_ctxt (v2,e2)
      | None ->
        failwith "invert only implemented for Fq"
    in
    let vlet = create_var false ps svlet ty in
    apply_rule (rrandom_oracle (i,j,k) (v1,e1) (v2,e2) vlet) ps

  | Rbad(i,sx) ->
    let ty =
      match Game.get_ju_gcmd ju i with
      | Game.GLet(_,e') when is_H e' ->
        let _,e = destr_H e' in
        e.e_ty
      | _ -> assert false
    in
    let vx = create_var false ps sx ty in
    apply_rule (rbad i vx) ps

  | Rexcept(i,es) ->
    let es = List.map (expr_of_parse_expr ps) es in
    apply_rule (rexcept i es) ps

  | Rexcept_oracle(op,es) ->
    let es = List.map (expr_of_parse_expr ps) es in
    apply_rule (rexcept_oracle op es) ps
   
  | Rrewrite_oracle(op,dir) ->
    apply_rule (rrewrite_oracle op dir) ps

  | Radd_test(op,t,aname,fvs) ->
    let t = expr_of_parse_expr ps t in
    let _, juoc = Game.get_ju_octxt ju op in
    let oty = juoc.Game.juoc_osym.Osym.dom in
    let destr_prod ty = match oty.ty_node with
      | Prod(tys) -> tys
      | _ -> [ty]
    in
    assert_msg (not (Ht.mem ps.ps_adecls aname))
      "radd_test: adversary with same name already declared";
    let asym = Asym.mk aname (mk_Prod []) oty in
    Ht.add ps.ps_adecls aname asym;
    let tys = destr_prod  oty in
    assert_msg (List.length fvs = List.length tys)
      "number of given variables does not match type";
    let fvs = List.map2 (fun v ty -> create_var false ps v ty) fvs tys in
    apply_rule (radd_test op t asym fvs) ps

let pp_goals fmt gs = 
  match gs with
  | None -> Format.printf "No goals@\n"
  | Some [] -> Format.printf "No remaining goals, proof completed.@\n"
  | Some jus ->
    let pp_goal i ju =
      Format.fprintf fmt "goal %i:@\n%a@\n@\n" (i + 1) Game.pp_ju ju in
    List.iteri pp_goal jus 

let handle_instr ps instr =
  match instr with
  | Apply(tac) ->
    begin match ps.ps_goals with
    | Some(jus) -> handle_tactic ps tac jus
    | None -> assert false
    end
  | PrintGoals(s) ->
    Format.printf "@[<v>proof state %s:@\n%a@." s pp_goals ps.ps_goals;
    ps
  | RODecl(s,t1,t2) ->
    if Ht.mem ps.ps_rodecls s then
      failwith "random oracle with same name already declared.";
    Ht.add ps.ps_rodecls s
      (Hsym.mk s (ty_of_parse_ty ps t1) (ty_of_parse_ty ps t2));
    ps
  | EMDecl(s,g1,g2,g3) ->
    if Ht.mem ps.ps_emdecls s then
      failwith "bilinear map with same name already declared.";
    Ht.add ps.ps_emdecls s
      (Esym.mk s (create_groupvar ps g1) (create_groupvar ps g2) (create_groupvar ps g3));
    ps
  | ODecl(s,t1,t2) ->
      if Ht.mem ps.ps_odecls s then 
        failwith "oracle with same name already declared.";
    Ht.add ps.ps_odecls s 
      (Osym.mk s (ty_of_parse_ty ps t1) (ty_of_parse_ty ps t2));
    ps
  | ADecl(s,t1,t2) ->
    if Ht.mem ps.ps_adecls s then 
      failwith "adversary with same name already declared.";
    Ht.add ps.ps_adecls s 
      (Asym.mk s (ty_of_parse_ty ps t1) (ty_of_parse_ty ps t2));
    ps
  | AssmDec(s,g0,g1,priv) ->
    let ps' = ps_resetvars ps in
    let g0 = gdef_of_parse_gdef true ps' g0 in
    let g1 = gdef_of_parse_gdef true ps' g1 in
    let priv = List.fold_left (fun s x -> 
      try Vsym.S.add (Ht.find ps'.ps_vars x) s
      with Not_found -> failwith ("unknown variable "^x))
      Vsym.S.empty priv in
    if Ht.mem ps.ps_assm s then
      failwith "assumption with the same name already exists";
    Ht.add ps.ps_assm s (Assumption.mk_ad g0 g1 priv);
    ps
    
  | Judgment(gd, e) ->
    let ps = ps_resetvars ps in
    let ju = ju_of_parse_ju false ps gd e in
    { ps with ps_goals = Some([ju]) }

let eval_theory s =
  let pt = Parse.theory s in
  List.fold_left (fun ps i -> handle_instr ps i) (mk_ps ()) pt
