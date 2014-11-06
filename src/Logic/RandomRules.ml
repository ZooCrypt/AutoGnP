(*s Derived rules for dealing with random samplings. *)

(*i*)
open Abbrevs
open Util
open Nondet
open Type
open Syms
open Expr
open Game
open Rules
open NormField
open ParserUtil

module Ht = Hashtbl
module CR = CoreRules

let log_t ls = mk_logger "Logic.Derived" Bolt.Level.TRACE "RandomRules" ls
let _log_d ls = mk_logger "Logic.Derived" Bolt.Level.DEBUG "RandomRules" ls
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Derived rule for random sampling} *)

let parse_ctxt ts ju ty (sv,se) =
  let vmap = vmap_of_globals ju.ju_gdef in
  (* bound name overshadows names in game *)
  let v = Vsym.mk sv ty in
  Hashtbl.add vmap sv v;
  (v,expr_of_parse_expr vmap ts se)

let subst_ineq ju rv e =
  let ineqs = ref [] in
  let add_ineq e =
    if is_Not e then (
      let e = destr_Not e in
      if is_Eq e then (
         let (e1,e2) = destr_Eq e in
         if (ty_equal e1.e_ty mk_Fq) then (
           let e = mk_FMinus e1 e2 in
           if not (List.mem e !ineqs) then ineqs := e::!ineqs;
         )
      )
    )
  in
  let add_ineqs e =
    L.iter add_ineq (e_ty_outermost mk_Bool e)
  in
  iter_gdef_exp add_ineqs ju.ju_gdef;
  mconcat !ineqs >>= fun ie ->
  let inter = Se.inter (e_vars ie) (e_vars e) in
  mconcat (Se.elements inter) >>= fun iv ->
  log_t (lazy (fsprintf "ineq rewrite: replace %a by %a in expression %a\n%!"
                 pp_exp iv pp_exp ie pp_exp e));
  let erv = mk_V rv in
  let erv' = mk_V (Vsym.mk (CR.mk_name ()) erv.e_ty) in
  let eq = Norm.norm_expr_nice (mk_FMinus (e_replace erv erv' e) (e_replace iv ie e)) in
  guard (is_FPlus eq) >>= fun _ ->
  log_t (lazy (fsprintf  "ineq rewrite: solve %a for %a\n%!" pp_exp eq pp_exp erv'));
  let es = destr_FPlus eq in
  let (with_erv,without_erv) = L.partition (fun t -> Se.mem erv (e_vars t)) es in
  (match with_erv with
  | [ e ] ->
    if e_equal e (mk_FOpp erv) then ret (mk_FPlus without_erv)
    else if e_equal e erv then ret (mk_FOpp (mk_FPlus without_erv))
    else mempty
  | _ -> mempty
  ) >>= fun e ->
  ret (e_replace erv' erv e)

let transform_expr ju rv rvs mgen e =
  let erv = mk_V rv in
  let gvars = Game.write_gcmds ju.ju_gdef in
  let rves = L.map mk_V rvs in
  let evs = e_vars e in
  let factor_out_exprs =
    rves @ (Se.elements (Se.diff evs gvars))
    |> L.map (fun e -> if is_G e.e_ty then mk_GLog e else e)
    |> L.filter (fun fe -> ty_equal fe.e_ty mk_Fq)
    |> sorted_nub e_compare
    |> (fun xs -> let (us,vs) = L.partition is_GLog xs in us @ vs)
    
  in
  let aux fe =
    log_t (lazy (fsprintf "trying factor_out=%a" pp_exp fe));
    match polys_of_field_expr (CAS.norm id e) with
    | (nom, None) ->
      (*i v = v' * g + h => v' = (v - h) / g i*)
      let (g,_h) = factor_out fe nom in
      let e' = exp_of_poly g in
      guard (not (e_equal erv e')) >>= fun _ ->
      guard (Se.mem erv (e_vars e')) >>= fun _ ->
      log_t (lazy (fsprintf "transform expr=%a -> %a@\n%!" pp_exp e pp_exp e'));
      ret e'
    | _ -> mempty
  in
  match mgen with
   | None ->
     mplus (ret e) (msum (L.map aux factor_out_exprs))
   | Some ge ->
     let lge = mk_GLog ge in
     mplus
       (aux lge)
       (mplus
          (ret e)
          (msum (L.map aux (L.filter (fun fe -> not (e_equal fe lge)) factor_out_exprs))))

let contexts ju rv rvs mgen =
  (* find field expressions containing the sampled variable *)
  let es = ref [] in
  let add_subterms e =
    L.iter
      (fun fe ->
        if Se.mem (mk_V rv) (e_vars fe) && not (List.mem fe !es) && not (is_V fe)
        then es := !es @ [fe])
      (e_ty_outermost mk_Fq e)
  in
  iter_gdef_exp add_subterms ju.ju_gdef;
  add_subterms ju.ju_ev;
  mconcat !es >>= fun e ->
  log_t (lazy (fsprintf "possible expr=%a@\n%!" pp_exp e));
  transform_expr ju rv rvs mgen e >>= fun e ->
  mplus (ret e) (subst_ineq ju rv e) >>= fun e ->
  ret e

let t_rnd_pos ts mctxt1 mctxt2 ty rv rvs  mgen i ju = 
  log_t (lazy (fsprintf "t_rnd_pos: mgen = %a" (pp_opt pp_exp) mgen));
  (match mctxt2 with
  | Some (sv2,se2) -> ret (parse_ctxt ts ju ty (sv2,se2))
  | None           ->
    let e2s =
      run (-1) (contexts ju rv rvs mgen)
      |> L.map Norm.norm_expr_nice
      |> nub e_equal
    in
    mconcat e2s >>= fun e2 ->
    guard (not (e_equal (mk_FOpp (mk_V rv)) e2)) >>= fun () ->
    ret (rv,e2)
  ) >>= fun (v2,e2) ->
  log_t (lazy (fsprintf "t_rnd_pos: trying %a -> %a" Vsym.pp v2 pp_exp e2));
  (match mctxt1 with
  | Some(sv1,e1) -> ret (parse_ctxt ts ju ty (sv1,e1))
  | None when ty_equal ty mk_Fq ->
    ret (v2, DeducField.solve_fq_vars_known e2 v2)
  | None -> mempty
  ) >>= fun (v1,e1) ->
  CR.t_rnd i (v1,e1) (v2,e2) ju

let t_rnd_maybe ?i_rvars:(irvs=Vsym.S.empty) ts exact mi mctxt1 mctxt2 mgen ju =
  let samps = samplings ju.ju_gdef in
  let rvs = L.map (fun (_,(rv,_)) -> rv) samps in
  (match mi with
  | Some i -> ret i
  | None   -> mconcat (L.map fst samps)
  ) >>= fun i ->
  let (rv,(ty,es)) = L.assoc i samps in
  let vs = vars_dexc rv es in
  guard (ty_equal ty mk_Fq) >>= fun _ ->
  guard (not (Vsym.S.mem rv irvs)) >>= fun _ ->
  log_t (lazy "###############################");
  log_t (lazy (fsprintf "t_rnd_maybe %i\n%!" i));
  log_t (lazy (fsprintf "sampling: %i, %a@\n%!" i Vsym.pp rv));
  let rnd i = t_rnd_pos ts mctxt1 mctxt2 ty rv rvs mgen i in
  if exact then rnd i ju
  else
    ( t_swap_max ToEnd i vs @>= (fun i ->
      t_swap_others_max ToFront i @>= (fun i ->
      rnd i)))
    ju

(*i ----------------------------------------------------------------------- i*)
(* \hd{Random rule in oracle} *)

let parse_ctxt_oracle ts opos ju ty (sv,se) =
  let vmap = vmap_in_orcl ju opos in
  (* bound name overshadows names in game *)
  let v = Vsym.mk sv ty in
  Hashtbl.add vmap sv v;
  (v,expr_of_parse_expr vmap ts se)

let t_rnd_oracle_maybe ?i_rvars:(irvs=Vsym.S.empty) ts mopos mctxt1 mctxt2 ju =
  let osamps = osamplings ju.ju_gdef in
  let samps  = samplings ju.ju_gdef in
  let rvs = L.map (fun (_,(rv,_)) -> rv) samps in
  (match mopos with
  | Some opos -> ret opos
  | None      -> mconcat (L.map fst osamps)
  ) >>= fun ((i,j,k) as op) ->
  let (rv,(ty,_)) = L.assoc op osamps in
  guard (not (Vsym.S.mem rv irvs)) >>= fun _ ->
  log_t (lazy (fsprintf "###############################\n%!"));
  log_t (lazy (fsprintf "t_rnd_oracle_maybe (%i,%i,%i)\n%!" i j k));
  (match mctxt2 with
  | Some (sv2,se2) -> ret (parse_ctxt_oracle ts op ju ty (sv2,se2))
  | None           ->
    let e2s = run (-1) (contexts ju rv rvs None) in
    mconcat (sorted_nub e_compare (L.map Norm.norm_expr_nice e2s)) >>= fun e2 ->
    ret (rv,e2)
  ) >>= fun ((v2,e2)) ->
  log_t (lazy (fsprintf "trying %a -> %a@\n%!" Vsym.pp v2 pp_exp e2));
  (match mctxt1 with
  | Some(sv1,e1) -> ret (parse_ctxt_oracle ts op ju ty (sv1,e1))
  | None when ty_equal ty mk_Fq ->
    ret (v2, DeducField.solve_fq_vars_known e2 v2)
  | None -> mempty
  ) >>= fun (v1,e1) ->
  CR.t_rnd_oracle (i,j,k) (v1,e1) (v2,e2) ju

