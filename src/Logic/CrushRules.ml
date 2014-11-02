(*i*)
open Util
open Nondet
open Syms
open Expr
open Game
open Rules
open RewriteRules
open Assumption
open AssumptionRules
open RandomRules
open RindepRules
open CaseRules

module CR = CoreRules
module Ht = Hashtbl

let log_t ls =
  Bolt.Logger.log "Logic.Crush" Bolt.Level.TRACE ~file:"CrushRules" (Lazy.force ls)

let log_d ls =
  Bolt.Logger.log "Logic.Crush" Bolt.Level.DEBUG ~file:"CrushRules" (Lazy.force ls)

let log_i ls =
  Bolt.Logger.log "Logic.Crush" Bolt.Level.INFO ~file:"CrushRules" (Lazy.force ls)
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Simplification} *)

let t_split_ev_maybe mi ju =
  let ev = ju.ju_ev in
  (match mi with
  | Some i -> ret i
  | None   ->
    guard (is_Land ev) >>= fun _ ->
    mconcat (L.mapi (fun i e -> (i,e)) (destr_Land ev)) >>= fun (i,e) ->
    guard (is_Eq e) >>= fun _ ->
    let (a,b) = destr_Eq e in
    guard (is_Tuple a && is_Tuple b) >>= fun _ ->
    guard (L.length (destr_Tuple a) = L.length (destr_Tuple b)) >>= fun _ ->
    ret i
  ) >>= fun i ->
  CR.t_split_ev i ju

let t_rewrite_ev_maybe mi mdir ju =
  let ev = ju.ju_ev in
  (match mi with
  | Some i ->
    begin match mdir with
    | Some d -> ret (i,d)
    | None   -> mplus (ret (i,LeftToRight)) (ret (i,RightToLeft))
    end
  | None ->
    guard (is_Land ev) >>= fun _ ->
    let conjs = L.mapi (fun i e -> (i,e)) (destr_Land ev) in
    mconcat conjs >>= fun (i,e) ->
    let others = L.filter (fun (j,_) -> i <> j) conjs in
    let occ_others e' = L.exists (fun (_,e) -> e_exists (e_equal e') e) others in
    guard (is_Eq e) >>= fun _ ->
    let (a,b) = destr_Eq e in
    msum
      [ if (is_V a) || (is_H a && is_H b && occ_others a && e_compare a b > 0)
        then (ret LeftToRight) else mempty
      ; if (is_V b) || (is_H a && is_H b && occ_others b && e_compare b a > 0)
        then (ret RightToLeft) else mempty ] >>= fun dir ->
    ret (i,dir)
  ) >>= fun (i,dir) ->
  (CR.t_ensure_progress (CR.t_rw_ev i dir)) ju

let t_rewrite_oracle_maybe mopos mdir ju =
  (match mopos with
  | Some opos ->
    begin match mdir with
    | Some d -> ret (opos,d)
    | None   -> mplus (ret (opos,LeftToRight)) (ret (opos,RightToLeft))
    end
  | None ->
    mconcat (oguards ju.ju_gdef) >>= fun (opos,e) ->
    guard (is_Eq e) >>= fun _ ->
    let (a,b) = destr_Eq e in
    msum
      [ if (is_V a) then (ret LeftToRight) else mempty
      ; if (is_V b) then (ret RightToLeft) else mempty ] >>= fun dir ->
    ret (opos,dir)
  ) >>= fun (opos,dir) ->
  (CR.t_ensure_progress (CR.t_rewrite_oracle opos dir)) ju

let t_fix must_finish max t ju =
  let ps0 = first (CR.t_id ju) in
  let rec aux i ps =
    let gs = ps.CR.subgoals in
    let npss = mapM t gs in
    if (is_nil npss || i < 0)
    then (
      guard (not must_finish || ps.CR.subgoals = []) >>= fun _ -> 
      ret ps
    ) else (
      npss >>= fun pss ->
      let ps2 = CR.merge_proof_states pss ps.CR.validation in
      if list_equal ju_equal ps2.CR.subgoals ps.CR.subgoals then
        ret ps
      else
        aux (i - 1) ps2
    )
  in
  aux max ps0

let t_simp i must_finish _ts ju =
  let step =
    (   (t_norm ~fail_eq:true @|| CR.t_id)
     @> (    CR.t_false_ev 
         @|| t_rewrite_oracle_maybe None None
         @|| t_split_ev_maybe None
         @|| t_rewrite_ev_maybe None None))
  in
  t_fix i must_finish step ju

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Automated crush tactic} *)

type proof_search_info = {
  psi_assms  : Sstring.t;
  psi_rvars  : Vsym.S.t;
  psi_orvars : Vsym.S.t;
  psi_cases  : Se.t
}

let psi_empty = {
  psi_assms = Sstring.empty;
  psi_rvars = Vsym.S.empty;
  psi_orvars = Vsym.S.empty;
  psi_cases  = Se.empty
}

exception Disallowed

(* compute proof search information on path of each admit for given proof tree *)
let psis_of_pt pt =
  let admit_psis = ref [] in
  let rec aux psi pt =
    let gd = pt.CR.pt_ju.ju_gdef in
    let children = pt.CR.pt_children in
    match pt.CR.pt_rule with
    | CR.Rassm_dec(_,_,ad) ->
      let psi =
        { psi with psi_assms = Sstring.add ad.ad_name psi.psi_assms }
      in
      L.iter (aux psi) children
    | CR.Rcase_ev(_,e) ->
      let psi =
        { psi with psi_cases = Se.add e psi.psi_cases }
      in
      L.iter (aux psi) children    
    | CR.Rrnd(pos,_,_,_) ->
      let rands = samplings gd in
      let (rv,_) = L.assoc pos rands in
      let psi =
        { psi with psi_rvars = Vsym.S.add rv psi.psi_rvars }
      in
      L.iter (aux psi) children
    | CR.Rrnd_orcl(opos,_,_) ->
      let orands = osamplings gd in
      let (orv,_) = L.assoc opos orands in
      let psi =
        { psi with psi_orvars = Vsym.S.add orv psi.psi_orvars }
      in
      L.iter (aux psi) children
    | CR.Radmit "current" ->
      (* we ignore admits with label other from other branches of the proof *)
      admit_psis := psi::!admit_psis
    | _ ->
      L.iter (aux psi) children
  in
  aux psi_empty pt;
  !admit_psis

type stats = {
  nstates   : int;
  unqstates : int;
  jus       : judgment list
}

let log_games = false

let rec t_crush_step depth stats ts must_finish finish_now psi =
  let gdir = "games_h" in
  let ias = psi.psi_assms in
  let irvs = psi.psi_rvars in
  let iorvs = psi.psi_rvars in
  let icases = psi.psi_cases in
  (* let t_norm_xor_id = t_norm ~fail_eq:true @|| CR.t_id in *)
  let t_after_simp ju =
    let (jus,unqstates,is_old) =
      let ju = { ju with ju_gdef = L.sort compare ju.ju_gdef } in
      log_t (lazy (fsprintf "+++++ state: %i, unique state: %i@\n%a"
                     !stats.nstates !stats.unqstates pp_ju ju));
      if not (L.mem ju !stats.jus)
      then (ju::!stats.jus, !stats.unqstates + 1,false)
      else (!stats.jus, !stats.unqstates,true)
    in
    let s = fsprintf "%a" pp_ju ju in
    stats := { nstates = !stats.nstates + 1; unqstates = unqstates; jus = jus };
    if log_games then (
      Util.output_file (F.sprintf "%s/g%i.zc" gdir !stats.nstates)
        (s^(F.sprintf "\n depth %i\n" depth))
    );
    if is_old
    then CR.t_fail "state already explored!" ju
    else CR.t_id ju
  in
  let t_log s ju =
    if log_games then
      Util.append_file (F.sprintf "%s/g%i.zc" gdir !stats.nstates) s;
    CR.t_id ju
  in
  let t_prepare =
    (   (CR.t_ensure_progress (t_simp false 40 ts) @|| CR.t_id)
        @> (t_norm ~fail_eq:true @|| CR.t_id))
  in
  let t_close ju =
    ( (t_random_indep false @> t_log "random_indep")
      @|| (t_assm_comp ~icases ts false None None @> t_log "assm_comp")) ju
  in
  let t_progress = 
       (t_assm_dec ~i_assms:ias ts false None (Some LeftToRight) None None
        @> t_log "\nassm_dec")
    @| (t_rnd_maybe ~i_rvars:irvs ts false None None None @> t_log "\nrnd")
    @| (t_rexcept_maybe None None @> t_log "\nrexcept")
    @| (t_rnd_oracle_maybe ~i_rvars:iorvs ts None None None @> t_log "\nrnd_oracle")
    @| (t_add_test_maybe @> t_log "\nadd_test")
    @| (t_case_ev_maybe @> t_log "\ncase_ev")
  in
      (t_prepare @> t_after_simp)
   @> (    t_close
       @|| (if must_finish && finish_now then CR.t_fail "not finished" else t_progress))

and bycrush stats ts get_pt j ps1 =
  let step = t_crush_step j stats ts true in
  let psis = psis_of_pt (get_pt (prove_by_admit "current" ps1)) in
  let gs = ps1.CR.subgoals in
  assert (L.length gs = L.length psis);
  mapM (fun (psi,g) -> step (j <= 0) psi g) (L.combine psis gs) >>= fun pss ->
  let ps2 = CR.merge_proof_states pss ps1.CR.validation in
  if j > 1 then (
    mplus
      (guard (ps2.CR.subgoals = []) >>= fun _ -> ret ps2)
      (guard (ps2.CR.subgoals <> []) >>= fun _ -> bycrush stats ts get_pt (j - 1) ps2)
  ) else (
    (* return only finished pstates *)
    guard (ps2.CR.subgoals = []) >>= fun _ ->
    ret ps2
  )

and crush stats ts get_pt j ps1 =
  let step = t_crush_step j stats ts false in
  let psis = psis_of_pt (get_pt (prove_by_admit "current" ps1)) in
  let gs = ps1.CR.subgoals in
  assert (L.length gs = L.length psis);
  mapM (fun (psi,g) -> step (j <= 0) psi g) (L.combine psis gs) >>= fun pss ->
  let ps2 = CR.merge_proof_states pss ps1.CR.validation in
  if j > 1 then (
    (* return only proof states with exactly i steps *)
    crush stats ts get_pt (j - 1) ps2
  ) else (
    ret ps2
  )

and t_crush must_finish mi ts ps ju =
  let i = from_opt 5 mi in
  let get_pt ps' =
    CR.get_proof
      (prove_by_admit "others" (first (CR.apply_first (fun _ -> ret ps') ps)))
  in
  let stats = ref { nstates = 0; unqstates = 0; jus = [] } in
  if i > 0 then (
    let res =
      if must_finish then
        bycrush stats ts get_pt i (first (CR.t_id ju))
      else
        crush stats ts get_pt i (first (CR.t_id ju))
    in
    let s = match pull res with
      | Left _  -> "proof failed"
      | Right _ -> "proof found"
    in
    log_i
      (lazy (fsprintf "%s, visited %i proof states (%i unique).@\n%!"
               s !stats.nstates !stats.unqstates));
    res
  ) else (
    CR.t_fail "crush: number of steps cannot be smaller than one" ju
  )
