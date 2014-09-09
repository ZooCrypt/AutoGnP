(*i*)
open Util
open Nondet
open Syms
open Game
open Rules
open RewriteRules
open Assumption
open AssumptionRules
open RandomRules

module CR = CoreRules
module Ht = Hashtbl
(*i*)

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
    | CR.Radmit ->
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
    ((CR.t_cut ((t_norm ~fail_eq:true) @| CR.t_id))
     @> (   t_random_indep
         @| t_assm_dec ~i_assms:ias ts None (Some LeftToRight) None
         @| t_rnd_maybe ~i_rvars:irvs ts None None None
         @| t_rnd_oracle_maybe ~i_rvars:iorvs ts None None None))
  in
  let get_pt ps2 = prove_by_admit (first (CR.apply_first (fun _ -> ret ps2) ps)) in
  let rec aux j ps1 =
    let psis = psis_of_pt (get_pt ps1) in
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
