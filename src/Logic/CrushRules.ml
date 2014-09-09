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

exception Disallowed

let pt_allowed pt =
  let rec aux assumptions randoms pt =
    match pt.CR.pt_rule with
    | CR.Rassm_dec(_,_,ad) ->
      if L.mem ad.ad_name assumptions then raise Disallowed;
      L.iter (aux (ad.ad_name::assumptions) randoms) pt.CR.pt_children
    | CR.Rrnd(pos,_,_) ->
      let rands = samplings pt.CR.pt_ju.ju_gdef in
      let (rv,_) = L.assoc pos rands in
      eprintf "pt_allowed %a in %a" Vsym.pp rv (pp_list "," Vsym.pp) randoms;
      if L.mem rv randoms then raise Disallowed;
      L.iter (aux assumptions (rv::randoms)) pt.CR.pt_children
    | _ ->
      L.iter (aux assumptions randoms) pt.CR.pt_children
  in
  try aux [] [] pt; true with Disallowed -> false

let t_crush must_finish mi ts ps ju =

  let i = from_opt 5 mi in
  let step =
    (CR.t_cut ((t_norm ~fail_eq:true) @| CR.t_id))
    @> (   t_random_indep
        @| t_assm_dec ts None (Some LeftToRight) None
        @| t_rnd_maybe ts None None None)
  in
  let get_pt ps2 = prove_by_admit (first (CR.apply_first (fun _ -> ret ps2) ps)) in
  let rec aux j ps1 =
    let gs = ps1.CR.subgoals in
    mapM step gs >>= fun pss ->
    let ps2 = CR.merge_proof_states pss ps1.CR.validation in
    (* ps2 are the proof states reached after exactly i - j steps *)
    let pt = get_pt ps2 in
    guard (pt_allowed pt) >>= fun _ ->
    if j > 1 then
      mplus
        (* return finished proof states only when must_finish is used,
           otherwise, we are interested in proof states after exactly i-j steps *)
        (guard (must_finish && ps2.CR.subgoals = []) >>= fun _ ->
         ret ps2)
        (aux (j - 1) ps2)
    else
      (* return all proof states if must_finish is not given and finished ones otherwise *)
      (guard (not must_finish || ps2.CR.subgoals = []) >>= fun _ ->
       ret ps2)
  in
  aux i (first (CR.t_id ju))
