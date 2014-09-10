(*s Derived tactics for dealing with assumptions. *)

(*i*)
open Util
open Nondet
open Type
open Assumption
open Syms
open Expr
open Game
open TheoryState
open Rules
open RewriteRules

module Ht = Hashtbl
module CR = CoreRules
module PU = ParserUtil
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Decisional assumptions} *)

let _t_assm_dec assm dir subst ju =
  let c = 
    if dir = LeftToRight then assm.Assumption.ad_prefix1 
    else assm.Assumption.ad_prefix2
  in
  let jc = Util.take (L.length c) ju.ju_gdef in
  let subst = 
    L.fold_left2 (fun s i1 i2 ->
      match i1, i2 with
      | GLet(x1,_), GLet(x2,_) | GSamp(x1,_), GSamp(x2,_) 
        when Type.ty_equal x1.Vsym.ty x2.Vsym.ty ->
        Vsym.M.add x1 x2 s
      | _ -> tacerror "assumption_decisional : can not infer substitution")
      subst c jc in
  CR.t_assm_dec dir subst assm ju

let t_assm_dec_aux assm dir subst samp_assm lets_assm ju =
  let samp_gdef = samplings ju.ju_gdef in
  let samp_gdef = Util.take (L.length samp_assm) samp_gdef in
  (* subst renames assm into judgment *)
  guard (list_eq_for_all2
           (fun (_,(vs1,_)) (_,(vs2,_)) ->
             eprintf "check: %a=%a\n%!" Vsym.pp vs1 Vsym.pp vs2;
             ty_equal vs1.Vsym.ty vs2.Vsym.ty)
           samp_assm samp_gdef) >>= (fun _ ->
  eprintf "guard, %i %i\n%!" (L.length samp_assm) (L.length samp_gdef);
  let subst = 
    L.fold_left2
      (fun s (_,(vs1,_)) (_,(vs2,_)) ->Vsym.M.add vs1 vs2 s)
      subst
      samp_assm
      samp_gdef
  in
  eprintf "subst %a\n%!" (pp_list "," (pp_pair Vsym.pp Vsym.pp)) (Vsym.M.bindings subst);
  let ltac subst (i,((vs:Vsym.t),(e:expr))) =
    let name = mk_name () in
    let vs'  = Vsym.mk name vs.Vsym.ty in
    let e'   = Game.subst_v_e (fun vs -> Vsym.M.find vs subst) e in
    ( Vsym.M.add vs vs' subst
    , t_let_abstract i vs' (Norm.norm_expr e')
      (* @> t_guard (fun ju -> Se.mem (mk_V vs') (Game.read_ju ju) ) *)
    )
  in
  let priv_exprs = L.map (fun (_,(v,_)) -> mk_V v) samp_gdef in
  let (subst, let_abstrs) =  map_accum ltac subst lets_assm in
  eprintf "returned tactic@\n%!";
  try
    (        (* t_print "after swapping, before unknown"
          @>*) t_norm_unknown priv_exprs
          (* @> t_print "after unknown" *)
          @> t_seq_list let_abstrs
          (* @> t_print "after" *)
          @> CoreRules.t_assm_dec dir subst assm) ju
  with
    Invalid_rule s -> eprintf "%s%!"s; mempty)

let rec parallel_swaps old_new_pos =
  let upd_pos op np p =
    (* before: op .. p after p .. np*)
    if op < p && p >= np then p - 1
    (* before: p .. op after np .. p *)
    else if p < op && np <= p then p + 1
    else p
  in
  match old_new_pos with
  | [] -> []
  | (op,np)::old_new_pos ->
    (op,np - op)::parallel_swaps (L.map (fun (op',np') -> (upd_pos op np op',np')) old_new_pos)

(** Fuzzy matching with given assumption, try out swap and
    let abstractions that make assumption applicable. *)
let t_assm_dec_auto assm dir subst ju =
  eprintf "###############################\n%!";
  eprintf "t_assm_dec_auto dir=%s assm=%s\n%!" (string_of_dir dir) assm.Assumption.ad_name;
  let assm_cmds =
    match dir with
    | LeftToRight -> assm.Assumption.ad_prefix1 
    | RightToLeft -> assm.Assumption.ad_prefix2
  in
  let samp_assm = samplings assm_cmds in
  let lets_assm = lets assm_cmds in
  let samp_gdef = samplings ju.ju_gdef in
  eprintf "@[assm:@\n%a@\n%!@]" (pp_list "@\n" pp_samp) samp_assm;
  eprintf "@[assm:@\n%a@\n%!@]" (pp_list "@\n" pp_let)  lets_assm;
  eprintf "@[gdef:@\n%a@\n%!@]" (pp_list "@\n" pp_samp) samp_gdef;
  (* FIXME: we assume that the samplings in the assumption occur first
     and are of type Fq *)
  let assm_samp_num = L.length samp_assm in
  let samp_gdef = List.filter (fun (_,(_,(ty,_))) -> ty_equal ty mk_Fq) samp_gdef in
  pick_set_exact assm_samp_num (mconcat samp_gdef) >>= fun match_samps ->
  eprintf "matching %a\n%!" (pp_list "," pp_int) (L.map fst match_samps);
  permutations match_samps >>= fun match_samps ->
  eprintf "matching permutation %a\n%!"
    (pp_list "," (pp_pair pp_int Vsym.pp))
    (L.map (fun x -> (fst x, fst (snd x))) match_samps);
  let old_new_pos = L.mapi (fun i x -> (fst x,i)) match_samps in
  let swaps =
    L.map
      (fun (old_pos,delta) -> eprintf "rswap %i %i\n%!" old_pos delta; CR.t_swap old_pos delta)
      (parallel_swaps old_new_pos)
  in
  (t_seq_list swaps @> t_assm_dec_aux assm dir subst samp_assm lets_assm) ju

(** Supports placeholders for which all possible values are tried *)
let t_assm_dec ?i_assms:(iassms=Sstring.empty) ts massm_names mdir mvnames ju =
  (* use assumption with given name or try all decisional assumptions *)
  (match massm_names with
   | Some aname ->
     begin try ret (Ht.find ts.ts_assms_dec aname)
     with Not_found -> tacerror "error no assumption %s" aname
     end
   | None ->
     mconcat (Ht.fold (fun _aname assm acc -> assm::acc) ts.ts_assms_dec [])
  ) >>= fun assm ->
  guard (not (Sstring.mem assm.ad_name iassms)) >>= fun _ ->
  (* use given direction or try both directions *)
  (opt ret (mconcat [LeftToRight; RightToLeft]) mdir)
  >>= fun dir ->
  (* generate substitution for all required new variable names
     generating new variable names if not enough are provided *)
  let needed = Assumption.needed_var dir assm in
  let given_vnames = from_opt [] mvnames in
  let required = max 0 (L.length needed - L.length given_vnames) in
  (* FIXME: prevent variable clashes here *)
  let generated_vnames = L.map (fun _ -> mk_name ()) (list_from_to 0 required) in
  let subst = 
    L.fold_left2
      (fun sigma v x -> Vsym.M.add v (Vsym.mk x v.Vsym.ty) sigma)
      Vsym.M.empty
      needed
      (given_vnames@generated_vnames)
  in
  t_assm_dec_auto assm dir subst ju

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Derived tactics for dealing with computational assumptions} *)

let t_assm_comp ts maname mev_e ju =
  (match maname with
  | Some aname ->
    begin try ret (Ht.find ts.ts_assms_comp aname)
    with Not_found -> tacerror "error no assumption %s" aname
    end
  | None ->
    mconcat (Ht.fold (fun _aname assm acc -> assm::acc) ts.ts_assms_comp [])
  ) >>= fun assm ->
  (match mev_e with
  | Some se ->
    let vmap = vmap_of_globals ju.ju_gdef in
    ret (PU.expr_of_parse_expr vmap ts se)
  | None ->
    mempty
  ) >>= fun ev_e ->
  let c = assm.Assumption.ac_prefix in
  let jc = Util.take (L.length c) ju.ju_gdef in
  let subst =
    L.fold_left2 (fun s i1 i2 ->
      match i1, i2 with
      | GLet(x1,_), GLet(x2,_) | GSamp(x1,_), GSamp(x2,_) 
        when Type.ty_equal x1.Vsym.ty x2.Vsym.ty ->
        Vsym.M.add x1 x2 s
      | _ ->
        tacerror "assumption_computational : can not infer substitution")
      Vsym.M.empty c jc
  in
  CR.t_assm_comp assm ev_e subst ju
