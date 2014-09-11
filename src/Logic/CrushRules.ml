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

module CR = CoreRules
module Ht = Hashtbl
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
    mconcat (L.mapi (fun i e -> (i,e)) (destr_Land ev)) >>= fun (i,e) ->
    guard (is_Eq e) >>= fun _ ->
    let (a,b) = destr_Eq e in
    mplus 
      (if (is_V a) then (ret LeftToRight) else mempty)
      (if (is_V b) then (ret RightToLeft) else mempty) >>= fun dir ->
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
    mplus 
      (if (is_V a) then (ret LeftToRight) else mempty)
      (if (is_V b) then (ret RightToLeft) else mempty) >>= fun dir ->
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
      aux (i - 1) ps2
    )
  in aux max ps0

let t_simp i must_finish _ts ju =
  let step ju =
        ((CR.t_cut ((t_norm ~fail_eq:true) @| CR.t_id))
     @> (    CR.t_false_ev 
         @|| t_rewrite_oracle_maybe None None
         @|| t_split_ev_maybe None
         @|| t_rewrite_ev_maybe None None )) ju
  in
  t_fix i must_finish step ju

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Automated crush tactic} *)


type proof_search_info = {
  psi_assms  : Sstring.t;
  psi_rvars  : Vsym.S.t;
  psi_orvars : Vsym.S.t
}

let psi_empty = {
  psi_assms = Sstring.empty;
  psi_rvars = Vsym.S.empty;
  psi_orvars = Vsym.S.empty
}

exception Disallowed

(* compute proof search information on path of each admit
   for given proof tree *)
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
    | CR.Rrnd(pos,_,_) ->
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
      (* we ignore admit's with label other from other branches of the proof *)
      admit_psis := psi::!admit_psis
    | _ ->
      L.iter (aux psi) children
  in
  aux psi_empty pt;
  !admit_psis

let t_crush must_finish mi ts ps ju =
  let i = from_opt 5 mi in
  (* ps2 are the proof states reached after exactly i - j steps *)

  let step psi =
    let ias = psi.psi_assms in
    let irvs = psi.psi_rvars in
    let iorvs = psi.psi_rvars in
    let t_norm_xor_id = t_norm ~fail_eq:true @|| CR.t_id in
    (   t_norm_xor_id
     @> (    (((t_simp false 10 ts @> t_norm_xor_id) @|| CR.t_id)
              @> (t_random_indep (* @|| t_assm_comp ts None None *)))
         @|| (   t_simp true 10 ts
              @| t_assm_dec ~i_assms:ias ts false None (Some LeftToRight) None
              @| t_rnd_maybe ~i_rvars:irvs ts false None None None
              @| t_rnd_oracle_maybe ~i_rvars:iorvs ts None None None)))
  in
  let get_pt ps2 =
    CR.get_proof (prove_by_admit "others" (first (CR.apply_first (fun _ -> ret ps2) ps)))
  in
  let rec aux j ps1 =
    let psis = psis_of_pt (get_pt (prove_by_admit "current" ps1)) in
    let gs = ps1.CR.subgoals in
    assert (L.length gs = L.length psis);
    mapM (fun (psi,g) -> step psi g) (L.combine psis gs) >>= fun pss ->
    let ps2 = CR.merge_proof_states pss ps1.CR.validation in
    if j > 1 then (
      if must_finish then (
        mplus
          (guard (ps2.CR.subgoals = []) >>= fun _ -> ret ps2)
          (guard (ps2.CR.subgoals <> []) >>= fun _ -> aux (j - 1) ps2)
      ) else (
        (* return only proof states with exactly i steps for must_finish=false *)
        (aux (j - 1) ps2)
      )
    ) else (
      (* return all proof states if must_finish is not given and finished ones otherwise *)
      (guard (not must_finish || ps2.CR.subgoals = []) >>= fun _ ->
       ret ps2))
  in
  aux i (first (CR.t_id ju))



