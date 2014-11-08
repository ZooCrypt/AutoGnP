(*s Simplification rules *)

(*i*)
open Abbrevs
open Util
open Nondet
open Syms
open Expr
open ExprUtils
open Type
open Game
open Rules
open CoreTypes
open RewriteRules

module CR = CoreRules
module CT = CoreTypes
module Ht = Hashtbl

let _log_t ls  = mk_logger "Logic.Crush" Bolt.Level.TRACE "CrushRules" ls
let _log_d ls = mk_logger "Logic.Crush" Bolt.Level.DEBUG "CrushRules" ls
let log_i ls  = mk_logger "Logic.Crush" Bolt.Level.INFO  "CrushRules" ls
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Simplification} *)

let t_split_ev_maybe mi ju =
  let ev = ju.ju_se.se_ev in
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
  let ev = ju.ju_se.se_ev in
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
      [ if is_V a || (is_H a && is_H b && occ_others a && e_compare a b > 0)
        then ret LeftToRight else mempty
      ; if is_V b || (is_H a && is_H b && occ_others b && e_compare b a > 0)
        then ret RightToLeft else mempty ] >>= fun dir ->
    ret (i,dir)
  ) >>= fun (i,dir) ->
  (CR.t_ensure_progress (CR.t_rw_ev i dir)) ju

let t_ctx_ev_maybe mi ju =
  log_i (lazy (fsprintf "ctx_ev_maybe: %i" (from_opt (-1) mi)));
  let ev = ju.ju_se.se_ev in
  (match mi with
  | Some i ->
    let conjs = destr_Land_nofail ev in
    let e = L.nth conjs i in
    ret (i,e)
  | None ->
    guard (is_Land ev) >>= fun _ ->
    let conjs = L.mapi (fun i e -> (i,e)) (destr_Land ev) in
    mconcat conjs >>= fun (i,e) ->
    ret (i,e)
  ) >>= fun (i,e) ->
  guard (is_Eq e) >>= fun _ ->
  let (e1,e2) = destr_Eq e in
  guard (ty_equal e1.e_ty mk_Fq) >>= fun _ ->
  let cv = Vsym.mk (CR.mk_name ju.ju_se) mk_Fq in
  let ce = mk_V cv in
  let diff,cdiff = if is_FZ e2 then (e1,ce) else (mk_FMinus e1 e2,mk_FMinus ce e2) in
  let c = mk_FDiv cdiff diff in
  log_i (lazy (fsprintf "ctx_ev_maybe: %i, %a" i pp_exp e));
  (CR.t_ctxt_ev i (cv,c) @> t_norm) ju

let t_rewrite_oracle_maybe mopos mdir ju =
  (match mopos with
  | Some opos ->
    begin match mdir with
    | Some d -> ret (opos,d)
    | None   -> mplus (ret (opos,LeftToRight)) (ret (opos,RightToLeft))
    end
  | None ->
    mconcat (oguards ju.ju_se.se_gdef) >>= fun (opos,e) ->
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
         @|| t_ctx_ev_maybe None
         @|| t_rewrite_ev_maybe None None))
  in
  t_fix i must_finish step ju
