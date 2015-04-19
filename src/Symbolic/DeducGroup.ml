(*s Deducibility for group expressions. *)

(*i*)
open Abbrevs
open Util
open Syms
open Type
open Expr
open ExprUtils
open NormField
open Norm
(*i*)

(* NOTE: For now, we do not deal with rational functions in the
   exponent. It might be possible to generalize the current algorithm
   by performing something similar to the cross-multiplication used to
   reduce equality of field-expressions to equality of ring-expressions. *)
let solve_group (emaps : Esym.t list) (ecs : (expr * inverter) list) e =
  log_i (lazy (fsprintf "solve_group %a |- %a"
                 (pp_list "," (pp_pair pp_exp pp_inverter)) ecs pp_exp e));

  (* helper functions *)
  let poly_of_expr e =
    let (nom, denom) = polys_of_field_expr (CAS.norm id e) in
    if denom<>None then failwith "solve_group: no support for rational functions";
    nom
  in
  let gexp e h =
    if is_FOne h then e
    else if is_FZ h then mk_GExp (mk_GGen (destr_G e.e_ty)) h
    else mk_GExp e h
  in
  let gmult e1 e2 =
    if is_GOne e1 then e2
    else if is_GOne e2 then e1
    else mk_GMult [e1; e2]
  in  
  (* returns polynomial and inverter polynomial *)
  let subtract_known f k_Fq =
    let covered_terms, remaining_terms =
      L.partition
        (fun (m,_i) ->
          Se.subset (se_of_list (L.map fst m)) (he_keys k_Fq))
        (EP.to_terms f)
    in
    if covered_terms<>[] then (
      let i_poly =
        exp_of_poly (EP.from_terms covered_terms)
        |> e_subst (me_of_list (L.map (fun (e,I e') -> (e,e')) (he_to_list k_Fq)))
      in
      let f = EP.from_terms remaining_terms in
      (f,i_poly)
    ) else (
      (f,mk_FZ)
    )
  in
  (* returns polynomial and inverter transformer *)
  let group_to_poly_simp subtract e gn k_Fq =
    let f = poly_of_expr (snd (destr_GExp e)) in
    (* NOTE: for now, we don't perform divide_known since this requires non-zero constraints *)
    let (f,i_poly) = subtract_known f k_Fq in
    if is_FNat i_poly
    then (f, id)
    else
      let i_poly = if subtract then mk_FOpp i_poly else i_poly in
      let inv_g = gexp (mk_GGen gn) i_poly in
      (f, fun i -> I (gmult (expr_of_inverter i) inv_g))
  in
  let gt = destr_G e.e_ty in

  (* known expressions / polynomials *)
  let known_Fq  = He.create 17 in
  let known_Gt  = Hep.create 17 in (* the group gt *)
  let known_Gs1 = Hep.create 17 in (* left source group for e : _ x _ -> gn (if exists) *)
  let known_Gs2 = Hep.create 17 in (* right source group *)

  (* register known expressions in Fq *)
  let register_known_fq (e,i) =
    if (is_FPlus e || is_FOpp e || is_FMult e) then (
      log_i (lazy (fsprintf "solve_group: known polynomial %a in Fq ignored" pp_exp e))
    ) else if is_Fq e.e_ty then (
      He.add known_Fq e i
    )
  in
  L.iter register_known_fq ecs;

  (* register known expressions in Gn *)
  let register_known k gn ((e,i) : expr * inverter) =
    if ty_equal e.e_ty (mk_G gn) then (
      let (f,i_trans) = group_to_poly_simp true e gn known_Fq in
      Hep.add k f (i_trans i)
    )
  in
  L.iter (register_known known_Gt gt) ecs;

  (* register expressions that can be computed by pairing expressions from source groups *)
  let em =
    try Some (L.find (fun es -> Groupvar.equal gt es.Esym.target) emaps)
    with Not_found -> None
  in
  begin match em with
  | None -> ()
  | Some em ->
    begin
      log_i (lazy (fsprintf "relevant map: %a" Esym.pp em));
      L.iter (register_known known_Gs1 em.Esym.source1) ecs;
      L.iter (register_known known_Gs2 em.Esym.source2) ecs;
      (* apply pairing to known group elements in source groups *)
      Hep.iter (fun f1 i1 ->
        Hep.iter (fun f2 i2 ->
          let ie1 = expr_of_inverter i1 in
          let ie2 = expr_of_inverter i2 in
          Hep.add known_Gt (EP.mult f1 f2) (I (mk_EMap em ie1 ie2)))
          known_Gs2)
        known_Gs1;
      (* known in source groups => known in target group (pair with generator) *)
      Hep.iter (fun f1 i1 ->
        let ie1 = expr_of_inverter i1 in
        Hep.add known_Gt f1 (I (mk_EMap em ie1 (mk_GGen em.Esym.source2))))
        known_Gs1;
      Hep.iter (fun f2 i2 ->
        let ie2 = expr_of_inverter i2 in
        Hep.add known_Gt f2 (I (mk_EMap em (mk_GGen em.Esym.source1) ie2)))
        known_Gs2
    end
  end;

  Hep.iter
    (fun f i -> log_i (lazy (fsprintf "known in exponent: %a with %a" EP.pp f pp_inverter i)))
    known_Gt;

  (* simplify secret by subtracting known (in Fq) terms *)
  let (f,i_trans) = group_to_poly_simp false e gt known_Fq in
  log_i (lazy (fsprintf "searching for exponent: %a @\n  with %a"
                 EP.pp f pp_inverter (i_trans (I (mk_V (Vsym.mk "[_]" e.e_ty))))));
  
  (* search for inverter by performing division with remainder in different orders *)
  let open Nondet in
  let search () =
    let k_Gt = Hep.fold (fun k _v l -> k::l) known_Gt [] in
    let rec go f i_trans unused =
      log_i (lazy (fsprintf ">>> go\n  f = %a\n  i_trans = %a\n  unused = (%a)"
                       EP.pp f pp_inverter (i_trans (I (mk_V (Vsym.mk "<_>" e.e_ty))))
                       (pp_list "," EP.pp) unused));

      if EP.is_const f then (
        (* f is a constant, we are done *)
        ret (i_trans (I (gexp (mk_GGen gt) (exp_of_poly f))))
      ) else (
        (* choose unknown polynomial h is known in exponent and try division *)
        mconcat unused >>= fun h ->
        let unused = L.filter (fun g -> not (EP.equal g h)) unused in
        let d = div_EP f h in
        let r = EP.(minus f (mult h d)) in

        log_i (lazy (fsprintf "try division by %a" EP.pp h));

        log_i (lazy (fsprintf "division:\n  f = %a\n  h = %a\n  d = %a\n  r = %a"
                       EP.pp f EP.pp h EP.pp d EP.pp r));

        let d, i_poly_d = subtract_known d known_Fq in
        let r, i_poly_r = subtract_known r known_Fq in
      
        log_i (lazy (fsprintf "d simpl: %a @\n  with %a" EP.pp d pp_exp i_poly_d));
        log_i (lazy (fsprintf "r simpl: %a @\n  with %a" EP.pp r pp_exp i_poly_r));
        if (EP.equal EP.zero d) then
          let i_trans = fun i ->
            let e1 = gmult (expr_of_inverter i) (gexp (mk_GGen gt) i_poly_r) in
            let e2 = gexp (expr_of_inverter (Hep.find known_Gt h)) i_poly_d in
            i_trans (I (gmult e1 e2))
          in
          go r i_trans unused
        else
          mempty
      )
    in
    go f i_trans k_Gt
  in
  match run 1 (search ()) with
  | I ie as i::_ ->
    let e' = norm_expr_strong (e_subst (me_of_list (L.map (fun (e,I e') -> (e',e)) ecs)) ie) in
    let e = norm_expr_strong e in
    if e_equal e e' then (
      log_i (lazy "#### found inverter");
      i
    ) else (
      log_i (lazy (fsprintf "#### wrong inverter@\n  inv = %a@\n  inv[known] = %a@\n  e = %a"
                     pp_exp ie pp_exp e' pp_exp e));
      raise Not_found
    )
  | []  -> raise Not_found
