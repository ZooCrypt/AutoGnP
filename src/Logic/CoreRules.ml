(*s Core rules of the logic. *)

(*i*)
open Abbrevs
open Util
open Nondet
open Syms
open Type
open Expr
open ExprUtils
(* open Gsyms *)
open Game
open Wf
open Assumption
open CoreTypes

let _log_t ls = mk_logger "Logic.Core" Bolt.Level.TRACE "CoreRules" ls
let _log_d ls = mk_logger "Logic.Core" Bolt.Level.DEBUG "CoreRules" ls
let _log_i ls = mk_logger "Logic.Core" Bolt.Level.INFO "CoreRules" ls
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Types for proofs and tactics} *)

(** Proof tree. *)
type 'a iproof_tree = {
  pt_children : ('a iproof_tree) list;
  pt_rule     : rule_name;
  pt_ju       : judgment;
  pt_info     : 'a
}

type proof_tree = unit iproof_tree

(** Replace subproofs with (possibly) different proofs of the same facts. *)
let pt_replace_children pt pts info =
  let equal_fact pt1 pt2 = ju_equal pt1.pt_ju pt2.pt_ju in
  assert (Util.list_eq_for_all2 equal_fact pt.pt_children pts);
  { pt with pt_children = pts; pt_info = info }

(** A goal is just a judgment (for now). *)
type goal = judgment

(** A rule takes a [goal] and returns a [rule_name] and the new goals. *)
type rule = goal -> rule_name * goal list

(** A validation is a proof tree with holes.
    It returns a proof tree given proof trees for the holes. *)
type validation = proof_tree list -> proof_tree

(** A proof state consists of the remaining goals and the validation. *)
type proof_state = {
  subgoals   : goal list;
  validation : validation
}

(** A tactic takes a goal and returns a proof state. *)
type tactic = goal -> proof_state nondet

(** A tactic that takes a goal and returns a result and a proof state. *)
type 'a rtactic = goal -> ('a * proof_state) nondet

(*i ----------------------------------------------------------------------- i*)
(* \hd{General purpose functions} *)

(** Create a variable name that is fresh in the given security experiment *)
let mk_name ?(name="r__") se =
  let vars = gdef_all_vars se.se_gdef in
  let name_of_int i = name^(string_of_int i) in
  let names =
    Vsym.S.fold
      (fun vs se -> Sstring.add (Id.name vs.Vsym.id) se) vars Sstring.empty
  in
  if Sstring.mem name names then
    let rec go n =
      let name = name_of_int n in
      if Sstring.mem name  names then go (n+1) else name
    in
    go 1
  else name 

(** Raised if there is no open goal. *)
exception NoOpenGoal

(** Prove goal [g] by rule [ru] which yields a rule name and subgoals. *)
let prove_by ru g =
  try
    let (rn,subgoals) = ru g in
    ret
      { subgoals = subgoals;
        validation = fun pts ->
          assert (L.length pts = L.length subgoals);
          assert (L.for_all2 (fun pt g -> ju_equal pt.pt_ju g) pts subgoals);
          { pt_ju       = g;
            pt_rule     = rn;
            pt_children = pts;
            pt_info     = ();
          }
      }
  with  
  | Invalid_rule s ->
    mfail (lazy s)
  | Wf.Wf_div_zero es ->
    mfail (lazy (fsprintf "Failed divzero check: %a" (pp_list "," pp_exp) es))
  | Wf.Wf_var_undef(vs,e,def_vars) ->
    mfail (lazy (fsprintf "Variable undefined: %a in %a not in %a"
                   Vsym.pp vs pp_exp e (pp_list "," Vsym.pp) (Vsym.S.elements def_vars)))

(** Get proof from proof state with no open goals. *)
let get_proof ps =
  if ps.subgoals <> [] then tacerror "get_proof: open subgoals remaining";
  ps.validation []

(** Given a list of proof states and a validation, create a new proof state
    with the combined subgoals and a combined validation. *)
let merge_proof_states pss validation =
  let rec validation' accu pss pts =
    match pss with
    | [] ->
      assert (pts = []);
      validation (L.rev accu)
    | ps::pss ->
      let hd, tl = Util.cut_n (L.length ps.subgoals) pts in
      validation' (ps.validation (L.rev hd) :: accu) pss tl
  in
  { subgoals   = conc_map (fun gs -> gs.subgoals) pss;
    validation = validation' [] pss }

(*i ----------------------------------------------------------------------- i*)
(* \hd{Tactic application} *)

(** Tactic that moves the first subgoal to the last position. *)
let move_first_last ps =
  match ps.subgoals with
  | [] -> tacerror "last: no goals"
  | ju :: jus ->
    let validation pts =
      match L.rev pts with
      | pt :: pts -> ps.validation (pt::L.rev pts)
      | _ -> assert false
    in
    { subgoals = jus @ [ju];
      validation = validation }

(** Apply the tactic [t] to the [n]-th subgoal of proof state [ps]. *)
let apply_on_n n t ps =
  let len = L.length ps.subgoals in
  if len = 0 then raise NoOpenGoal;
  if len <= n then tacerror "expected %i, got %i subgoal(s)" n len;
  let hd, g, tl = Util.split_n n ps.subgoals in
  t g >>= fun gsn ->
  let validation pts =
    let hd, tl = Util.cut_n n pts in
    let ptn, tl = Util.cut_n (L.length gsn.subgoals) tl in
    ps.validation (L.rev_append hd (gsn.validation (L.rev ptn) :: tl))
  in
  ret { subgoals = L.rev_append hd (gsn.subgoals @ tl);
        validation = validation }

(** Apply the tactic [t] to the first subgoal in proof state [ps]. *)
let apply_first t ps = apply_on_n 0 t ps

(** Apply the tactic [t] to all subgoals in proof state [ps]. *)
let apply_all t ps =
  mapM t ps.subgoals >>= fun pss ->
  ret (merge_proof_states pss ps.validation)

(** Apply the rtactic [t] to all subgoals in proof state [ps]
    and returns [t's] result. *)
let rapply_all rt ps =
  mapM rt ps.subgoals >>= fun pss ->
  match pss with
  | [y,ps2] ->
    ret (y,merge_proof_states [ps2] ps.validation)
  | _ ->
    mfail (lazy "t_bind: expected exactly one goal")

(*i ----------------------------------------------------------------------- i*)
(* \hd{Simple tactics and tacticals} *)

(** Identity tactic. *)
let t_id g = ret (
  { subgoals = [g];
    validation = fun pts -> match pts with [pt] -> pt | _ -> assert false })

(** Apply the given tactic and cut the search space by returning
    only the first possible proof state. *)
let t_cut t g =
  let pss = t g in
  match pull pss with
  | Left(Some s) -> mfail s
  | Left None    -> mfail (lazy "t_cut: mempty")
  | Right(x,_)   -> ret x

(** Sequential composition of the tactic [t1] with the tactic [t2]. *)
let t_seq t1 t2 g =
  t1 g >>= fun ps1 ->
  mapM t2 ps1.subgoals >>= fun ps2s ->
  ret (merge_proof_states ps2s ps1.validation)

(** Sequential composition of the tactic [t1] with the tactics [t2s]:
    apply [t1] to get $|t2s|$ new proof states [ps2s], then
    apply the i-th element of [t2s] to the i-th proof state in [ps2s]. *)
let t_seq_list t1 t2s g =
  t1 g >>= fun ps1 ->
  assert (L.length t2s = L.length ps1.subgoals);
  mapM (fun (t2,g) -> t2 g) (L.combine t2s ps1.subgoals) >>= fun ps2s ->
  ret (merge_proof_states ps2s ps1.validation)

(** Apply tactic [t1] to goal [g] or apply [t2] in case of failure. *)
let t_or tn1 tn2 g = Nondet.mplus (tn1 g)  (tn2 g)

(** Apply tactic [t] or [t_id] in case of failure. *)
let t_try t g = t_or t t_id g

(** Tactic that ignore the goal and fails with given format string. *)
let t_fail fs _g =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      _log_t (lazy s);
      mfail (lazy s))
    fbuf fs

(** Tactical that fails if the given tactic returns the same proof state. *)
let t_ensure_progress t g =
  t g >>= fun ps ->
  guard (not (L.length ps.subgoals = 1 && ju_equal (L.hd ps.subgoals) g)) >>= fun _ ->
  ret ps

(** Monadic bind for rtactics, expects that [t1] returns a single goal. *)
let t_bind (t1 : 'a rtactic) (ft2 : 'a -> 'b rtactic) g =
  t1 g >>= fun (x,ps1) ->
  mapM (ft2 x) ps1.subgoals >>= fun ps2s ->
  match ps2s with
  | [y,ps2] ->
    ret (y,merge_proof_states [ps2] ps1.validation)
  | _ ->
    mfail (lazy "t_bind: expected exactly one goal")

(** Monadic bind for a rtactic and a tactic. *)
let t_bind_ignore (t1 : 'a rtactic) (ft2 : 'a -> tactic) g =
  t1 g >>= fun (x,ps1) ->
  mapM (ft2 x) ps1.subgoals >>= fun ps2s ->
  ret (merge_proof_states ps2s ps1.validation)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Core rules: Helper functions} *)
(*i ----------------------------------------------------------------------- i*)

let ensure_gdef_eq rn a b =
  if not (gdef_equal a b) then 
    tacerror "%s: games not equal, @\n@[<hov 2>  %a@] vs @[<hov 2>  %a@]"
      rn (pp_gdef ~nonum:false) a (pp_gdef ~nonum:false) b

let ensure_event_eq rn e1 e2 =
  if not (ev_equal e1 e2) then
    tacerror "%s: events not equal, @\n@[<hov 2>  %a vs @ %a@]"
      rn pp_ev e1 pp_ev e2

let ensure_ren_inj rn ren =
  if not (ren_injective ren) then
    tacerror "%s: renaming not bijective" rn

let ensure_not_use rn used_vars forbidden_vars gdef =
  if not (se_disjoint used_vars forbidden_vars) then
    tacerror "%s: judgment uses private variables: %a in @\n@[<hv 2>%a@]" rn
      (pp_list "," pp_exp) (Se.elements (Se.inter used_vars forbidden_vars))
      (pp_gdef ~nonum:false) gdef

let ensure_ppt rn gdef =
  if not (is_ppt_gcmds gdef) then
    tacerror "%s: %a is not ppt" rn (pp_gdef ~nonum:false) gdef

let ensure_pr_Adv rn ju =
  if ju.ju_pr <> Pr_Adv then
    tacerror "%s: Adv judgment expected" rn

let ensure_pr_Succ_or_Adv rn ju =
  if ju.ju_pr <> Pr_Succ && ju.ju_pr <> Pr_Adv then
    tacerror "%s: Succ or Adv judgment expected" rn

(*i ----------------------------------------------------------------------- i*)
(* \hd{Core rules: Lossless bridging rules} *)
(*i ----------------------------------------------------------------------- i*)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Conversion.} *)

let rename_if_required rn se1 se2 =
  let ren = Game.unif_se se1 se2 in
  if Vsym.M.is_empty ren then se1
  else (
    ensure_ren_inj rn ren;
    subst_v_se (fun vs -> try Vsym.M.find vs ren with Not_found -> vs) se1
  )

let rconv do_norm_terms new_se ju =
  let rn = "conv" in
  let se = ju.ju_se in
  (* check well-formedness without DivZero and then unfold *)
  wf_se NoCheckDivZero se;
  wf_se NoCheckDivZero new_se;
  let se'     = norm_se ~norm:id se in
  let new_se' = norm_se ~norm:id new_se in
  (* perform renaming if required *)
  let se' = rename_if_required rn se' new_se' in
  (* check DivZero for unfolded+renamed and normalize (if requested) *)
  if not do_norm_terms then (
    ensure_gdef_eq  rn se'.se_gdef new_se'.se_gdef;
    ensure_event_eq rn se'.se_ev   new_se'.se_ev;
  ) else (
      (* try strong version first *)
      wf_se CheckDivZero se';
      wf_se CheckDivZero new_se';
      let norm_rw = map_se_exp Norm.norm_expr_strong in
      let se', new_se' = (norm_rw se', norm_rw new_se') in
      (* try *)
      ensure_gdef_eq  rn se'.se_gdef new_se'.se_gdef;
      ensure_event_eq rn se'.se_ev   new_se'.se_ev
      (*
      with
        _ ->
          (* try version that deals better with if afterwards *)
          let norm_rw = map_se_exp Norm.norm_expr_conv in
          let se', new_se' = (norm_rw se', norm_rw new_se') in
          ensure_gdef_eq  rn se'.se_gdef new_se'.se_gdef;
          ensure_event_eq rn se'.se_ev   new_se'.se_ev
      *)
  );
  Rconv, [{ ju with ju_se = new_se }]

let t_conv do_norm_terms new_se = prove_by (rconv do_norm_terms new_se)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Instruction swapping.} *)

let ensure_disjoint rn read write i c =
  let i = [i] in
  let ir = read i in
  let iw = write i in
  let cr = read c in
  let cw = write c in
  if not (se_disjoint iw cw && se_disjoint ir cw && se_disjoint cr iw) then
    tacerror "%s: can not swap" rn

let swap i delta ju =
  if delta = 0 then ju
  else (
    let se = ju.ju_se in
    let instr,{sec_left=hd; sec_right=tl; sec_ev=e} = get_se_ctxt se i in
    let c1,c2,c3 =
      if delta < 0 then
        let hhd, thd = cut_n (-delta) hd in
        thd, hhd, tl
      else
        let htl, ttl = cut_n delta tl in
        hd, L.rev htl, ttl
    in
    ensure_disjoint "swap" read_gcmds write_gcmds instr c2;
    if is_call instr && has_call c2 then tacerror "swap : can not swap";
    let c2,c3 =
      if delta > 0 then c2,instr::c3 else instr::c2,c3
    in
    let seoc = {sec_left=c1; sec_right=c3; sec_ev=e} in
    { ju with ju_se = set_se_ctxt c2 seoc }
  )

let rswap i delta ju = Rswap(i, delta), [swap i delta ju]

let t_swap i delta = prove_by (rswap i delta)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Instruction swapping for Oracle.} *)

let swap_oracle i delta ju =
  if delta = 0 then ju
  else (
    let se = ju.ju_se in
    let i, seoc = get_se_octxt se i in
    let c1_rev,c2,c3 =
      if delta < 0 then
        let hhd,thd = cut_n (-delta) seoc.seoc_cleft in
        thd,hhd,seoc.seoc_cright
      else
        let htl, ttl = cut_n delta seoc.seoc_cright in
        seoc.seoc_cleft, L.rev htl, ttl
    in
    ensure_disjoint "swap_oracle" read_lcmds write_lcmds i c2;
    let c2, c3 =
      if delta > 0 then c2, i::c3 else i::c2, c3
    in
    let seoc = { seoc with seoc_cleft = c1_rev; seoc_cright = c3} in
    { ju with ju_se = set_se_octxt c2 seoc }
  )

let rswap_oracle i delta ju =
  Rswap_orcl(i,delta), [swap_oracle i delta ju]

let t_swap_oracle i delta = prove_by (rswap_oracle i delta)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Random sampling.} *)

let ensure_bijection se c1 c2 rs =
  (* v : t
     c1 : t' -> t
     c2 : t  -> t' *)
  let dty1,cty1 = ctxt_ty c1 in
  let dty2,cty2 = ctxt_ty c2 in
  let t = rs.Vsym.ty in
  let t' = dty1 in
  if not (ty_equal cty1 t) then
    tacerror "rnd: c1 has type %a -> %a while %a -> %a is expected"
      pp_ty dty1 pp_ty cty1 pp_ty t' pp_ty t;
  if not (ty_equal dty2 t && ty_equal cty2 t') then
    tacerror "rnd: c2 has type %a -> %a while %a -> %a is expected"
      pp_ty dty2 pp_ty cty2 pp_ty t pp_ty t';

  let v  = mk_V rs in
  let v' = mk_V (Vsym.mk (mk_name ~name:"v__" se) t') in
  if not (Norm.e_equalmod (inst_ctxt c2 (inst_ctxt c1 v')) v' &&
            Norm.e_equalmod (inst_ctxt c1 (inst_ctxt c2 v)) v) then
    tacerror "rnd: contexts %a and %a are not bijective"
      pp_ctxt c1 pp_ctxt c2

(*  if not (ty_equal_size dty1 dty2) then
    tacerror "rnd: invalid size type for contexts" *)

let rrnd p c1 c2 ju =
  let se = ju.ju_se in
  match get_se_ctxt se p with
  | GSamp(rvs,(_,exc)), sec ->
    if exc <> [] then tacerror "rnd: excepted distribution not allowed";
    let new_ty = (fst c1).Vsym.ty in
    ensure_bijection se c1 c2 rvs;
    (* check second context first such that divZero does not clobber undef *)
    let wfs = wf_gdef NoCheckDivZero (L.rev sec.sec_left) in
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c2)) (snd c2);
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c1)) (snd c1);
    let rv = mk_V rvs in
    let nrvs = 
      if ty_equal rvs.Vsym.ty new_ty then rvs 
      else Vsym.mk (mk_name ~name:(Id.name (fst c1).Vsym.id) se) new_ty in
    let nrv = mk_V nrvs in
    let vslet = Vsym.mk (mk_name ~name:"u__" se) rv.e_ty in
    let cmds = [ GSamp(nrvs,(new_ty, [])); GLet(vslet, inst_ctxt c1 nrv) ] in
    let subst e = e_replace rv (mk_V vslet) e in
    let sec = { sec with
                sec_right = map_gdef_exp subst sec.sec_right;
                sec_ev    = map_ev_exp subst sec.sec_ev }
    in
    Rrnd(p,nrvs,c1,c2), [ { ju with ju_se = set_se_ctxt cmds sec } ]
  | _ ->
    tacerror "rnd: position given is not a sampling"

let t_rnd p c1 c2 = prove_by (rrnd p c1 c2)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Random sampling in oracle.} *)

let rrnd_oracle p c1 c2 ju =
  let se = ju.ju_se in
  match get_se_octxt se p with
  | LSamp(rvs,(_,exc)), seoc ->
    if exc <> [] then tacerror "rnd_oracle: excepted distribution not allowed";
    let new_ty = (fst c1).Vsym.ty in
    ensure_bijection se c1 c2 rvs;
    (* check second context first such that divZero does not clobber undef *)
    let wfs = wf_gdef CheckDivZero (L.rev seoc.seoc_sec.sec_left) in
    let wfs = ensure_varnames_fresh wfs seoc.seoc_oargs in
    let wfs = wf_lcmds CheckDivZero wfs None (L.rev seoc.seoc_cleft) in
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c2)) (snd c2);
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c1)) (snd c1);
    let rv = mk_V rvs in
    let qual = Qual seoc.seoc_osym in
    let nrvs = 
      if ty_equal rvs.Vsym.ty new_ty then rvs 
      else Vsym.mk_qual (mk_name ~name:(Id.name (fst c1).Vsym.id) se) qual new_ty
    in
    let nrv = mk_V nrvs in
    let vslet = Vsym.mk_qual (mk_name ~name:"u__" se) qual rv.e_ty in
    let cmds = [ LSamp(nrvs,(new_ty, [])); LLet(vslet, inst_ctxt c1 nrv) ] in
    let subst e = e_replace rv (mk_V vslet) e in
    let sec =
      { seoc.seoc_sec with
        sec_right = map_gdef_exp subst seoc.seoc_sec.sec_right;
        sec_ev    = map_ev_exp subst seoc.seoc_sec.sec_ev }
    in
    let seoc =
      { seoc with
        seoc_return = subst seoc.seoc_return;
        seoc_cright = L.map (map_lcmd_exp subst) seoc.seoc_cright;
        seoc_sec = sec }
    in
    Rrnd_orcl(p,c1,c2), [ { ju with ju_se = set_se_octxt cmds seoc } ]
  | _ -> tacerror "rnd_oracle: position given is not a sampling"

let t_rnd_oracle p c1 c2 = prove_by (rrnd_oracle p c1 c2)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Copy condition implied by event to assert.} *)

let rassert p e ju =
  let se = ju.ju_se in
  let cmd, sec = get_se_ctxt se p in
  assert (ty_equal e.e_ty mk_Bool);
  (* check that e well-defined at desired position, exploits
     uniqueness of variables, i.e., v defined => v remains unchanged *)
  let wfs = wf_gdef NoCheckDivZero (L.rev sec.sec_left) in
  wf_exp CheckDivZero wfs e;
  let cmds = [ GAssert(e); cmd ] in
  let ju1 =
    { ju_pr = Pr_Succ;
      ju_se = { se with se_ev = 
                { se.se_ev with 
                  ev_expr = mk_Land [se.se_ev.ev_expr; mk_Not e]; } } }
  in
  let ju2 = { ju with ju_se = set_se_ctxt cmds sec } in
  Rassert(p,e), [ ju1; ju2 ]

let t_assert p e = prove_by (rassert p e)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Rewrite oracle using test.} *)

let rrewrite_oracle op dir ju =
  let se = ju.ju_se in
  match get_se_octxt se op with
  | LGuard(t) as lc, seoc ->
    let (a,b) =
      match t.e_node with
      | App(Eq,[u;v]) -> if dir = LeftToRight then (u,v) else (v,u)
      | _ -> tacerror "rewrite_oracle: can only rewrite equalities"
    in
    let subst e = e_replace a b e in
    let seoc =
      { seoc with
        seoc_cright = L.map (map_lcmd_exp subst) seoc.seoc_cright;
        seoc_return = subst seoc.seoc_return }
    in
    Rrw_orcl(op,dir), [ { ju with ju_se = set_se_octxt [lc] seoc } ]
  | _ ->
    tacerror "rewrite_oracle: invalid position"

let t_rewrite_oracle op dir = prove_by (rrewrite_oracle op dir)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Merge conjucts in event with equalities} *)

let merge_base_event ev1 ev2 =
  match ev1.e_node, ev2.e_node with
  | App (Eq,[e11;e12]), App(Eq,[e21;e22]) ->
    mk_Eq (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22])
  | _, _ -> failwith "merge_ev: cannot merge the given events"

let rmerge_ev i j ju =
  let se = ju.ju_se in
  let i,j = if i <= j then i, j else j, i in
  let evs = destr_Land_nofail se.se_ev.ev_expr in
  let l,b1,r = Util.split_n i evs in
  let l',b2,r =
    if i = j then [], b1, r
    else Util.split_n (j - i - 1) r
  in
  let ev = merge_base_event b1 b2 in
  let evs = L.rev_append l (L.rev_append l' (ev::r)) in
  let new_se = {se with se_ev = { se.se_ev with ev_expr = mk_Land evs} } in
  Rmerge_ev(i,j), [ { ju with ju_se = new_se } ]

let t_merge_ev i j = prove_by (rmerge_ev i j)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Split (in)equality on tuples into multiple equalities} *)

let rsplit_ev i ju =
  let rn = "split_ev" in
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev.ev_expr in
  if i < 0 || i >= L.length evs then
    tacerror "%s: invalid event position %i" rn i;
  let l,b,r = Util.split_n i evs in
  let b =
    if not (is_Eq b)
      then tacerror "rsplit_ev: bad event, expected equality";
    let (e1,e2) = destr_Eq b in
    if not (is_Tuple e1 && is_Tuple e2)
      then tacerror "rsplit_ev: bad event, expected tuples, %a and %a" pp_exp e1 pp_exp e2;
    let es1, es2 = destr_Tuple e1, destr_Tuple e2 in
    if not (L.length es1 = L.length es2)
      then tacerror "rsplit_ev: bad event, got tuples of different lengths, %a and %a" pp_exp e1 pp_exp e2;
    L.map (fun (e1,e2) -> mk_Eq e1 e2) (L.combine es1 es2)
  in
  let evs = l@b@r in
  let new_se = { se with se_ev = { se.se_ev with ev_expr = mk_Land evs }} in
  Rsplit_ev(i), [ { ju with ju_se = new_se } ]

let t_split_ev i = prove_by (rsplit_ev i)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Use equality conjunct to rewrite other conjuncts} *)

let rrw_ev i d ju =
  let rn = "rewrite_ev" in
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev.ev_expr in
  if i < 0 || i >= L.length evs then
    tacerror "%s: invalid event position %i" rn i;
  let l,b,r = Util.split_n i evs in
  let u,v =
    if is_Eq b then (
      let u,v = destr_Eq b in
      if d = LeftToRight then (u,v) else (v,u)
    ) else if is_Not b && is_Eq (destr_Not b) then (
      let eq = destr_Not b in
      if d = LeftToRight then (eq,mk_False)
      else tacerror "%s: inequality can only be used from left to right" rn
    ) else (
      tacerror "%s: bad event, expected equality or inequality" rn
    )
  in
  let subst e = e_replace u v e in
  let evs = (L.map subst l |> L.rev)@[b]@(L.map subst r) in
  let new_se = { se with se_ev = {se.se_ev with ev_expr = mk_Land evs } } in
  Rrw_ev(i,d), [ { ju with ju_se = new_se } ]

let t_rw_ev i d = prove_by (rrw_ev i d)

(*i ----------------------------------------------------------------------- i*)
(* {\bf Swap sampling from once-oracle to main.} *)

let rswap_main ((i,j,k) as opos_eq) vname ju =
  let se = ju.ju_se in
  match get_se_octxt se (i,j,k,Ohyb OHeq) with
  | LSamp(vs,d),seoc ->
    let vs_new = Vsym.mk vname vs.Vsym.ty in
    let subst e = e_replace (mk_V vs) (mk_V vs_new) e in
    let samp = GSamp(vs_new,d) in
    let sec =
      { sec_left  = samp::seoc.seoc_sec.sec_left;
        sec_right = map_gdef_exp subst seoc.seoc_sec.sec_right;
        sec_ev    = map_ev_exp subst seoc.seoc_sec.sec_ev;
      }
    in
 
    let seoc =
      { seoc with
          seoc_sec = sec;
          seoc_cleft = L.map (map_lcmd_exp subst) seoc.seoc_cleft;
          seoc_cright = L.map (map_lcmd_exp subst) seoc.seoc_cright;
          seoc_return = subst seoc.seoc_return }
    in
    let se = set_se_octxt [] seoc in
    wf_se NoCheckDivZero se;
    Rswap_main opos_eq, [ { ju with ju_se = se } ]
  | _ ->
    assert false

let t_swap_main opos vname =
  prove_by (rswap_main opos vname)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Core rules: Bridging rules with small loss} *)
(*i ----------------------------------------------------------------------- i*)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Sampling from excepted distribution.} *)

let rexcept p es ju =
  let se = ju.ju_se in
  let len = L.length se.se_gdef in
  if not (p < len) && p >= 0 then
    tacerror "except: invalid position, %i not between 1 and %i" (p+1) len;
  match get_se_ctxt se p with
  | GSamp(_,(_,es')), _ when list_equal e_equal es' es ->
    tacerror "except: identical exceptions already present"    
  | GSamp(vs,(t,_)), sec ->
    let se = set_se_ctxt [ GSamp(vs,(t,es)) ] sec in
    wf_se NoCheckDivZero se;
    Rexc(p, es), [ {ju with ju_se = se } ]
  | _ ->
    tacerror "except: position given is not a sampling"

let t_except p es = prove_by (rexcept p es)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Sampling from excepted distribution for oracle.} *)

let rexcept_oracle p es ju =
  let se = ju.ju_se in
  match get_se_octxt se p with
  | LSamp(_,(_,es')), _ when list_equal e_equal es' es ->
    tacerror "except_oracle: identical exceptions already present"    
  | LSamp(vs,(t,_)), seoc ->
    let se = set_se_octxt [LSamp(vs,(t,es))] seoc in
    Rexc_orcl(p,es), [ { ju with ju_se = se } ]
  | _ -> tacerror "except_oracle: position given is not a sampling"

let t_except_oracle p es = prove_by (rexcept_oracle p es)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Core rules: Weaken event} *)
(*i ----------------------------------------------------------------------- i*)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Perform case distinction on event.} *)

let conj_or_negation_included e ev =
  let norm = Norm.norm_expr_weak in
  let evs = L.map norm (destr_Land_nofail ev) in
  (L.mem (norm e) evs || L.mem (norm (mk_Not e)) evs)

let rcase_ev ?flip:(flip=false) ?allow_existing:(ae=false) e ju =
  let se = ju.ju_se in
  ensure_pr_Succ_or_Adv "case_ev" ju;
  let ev = se.se_ev.ev_expr in
  if not ae && conj_or_negation_included e ev then
    tacerror "case_ev: event or negation already in event";
  let ju1 = { ju with ju_se =
      { se with se_ev = { se.se_ev with ev_expr = mk_Land [ev;e] }}} in
  let ju2 = { ju with ju_se = 
      { se with se_ev = { se.se_ev with ev_expr = mk_Land [ev; mk_Not e] }}} in
  Rcase_ev(flip,e), if flip then [ju2; ju1] else [ju1;ju2]

let t_case_ev ?flip:(flip=false) ?allow_existing:(ae=false) e =
  prove_by (rcase_ev ~flip ~allow_existing:ae e)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Apply context to event} *)

let rctxt_ev i c ju =
  ensure_pr_Succ_or_Adv "ctxt_ev" ju;
  let se = ju.ju_se in
  let ev = se.se_ev.ev_expr in
  let evs = destr_Land_nofail ev in
  if i < 0 || i >= L.length evs then failwith "invalid event position";
  let l,b,r = Util.split_n i evs in
  let b =
    if is_Eq b then
      let (e1,e2) = destr_Eq b in
      mk_Eq (inst_ctxt c e1) (inst_ctxt c e2)
    else tacerror "ctxt_ev: bad event, expected equality"
  in
  let ev = mk_Land (L.rev_append l (b::r)) in
  let wfs = wf_gdef NoCheckDivZero (se.se_gdef) in
  wf_exp NoCheckDivZero wfs ev;
  let new_ju = { se with se_ev = { se.se_ev with ev_expr = ev } } in
  Rctxt_ev(i,c), [ { ju with ju_se = new_ju } ]

let t_ctxt_ev i c = prove_by (rctxt_ev i c)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Remove an event} *)

let rremove_ev (rm:int list) ju =
  ensure_pr_Succ_or_Adv "ctxt_ev" ju;
  let se = ju.ju_se in
  let evs =
    destr_Land_nofail se.se_ev.ev_expr
    |> L.mapi (fun i e -> if L.mem i rm then None else Some e)
    |> cat_Some
  in
  let new_ju = { se with se_ev = 
      { se.se_ev with ev_expr = if evs = [] then mk_True else mk_Land evs }} in
  Rremove_ev rm, [ { ju with ju_se = new_ju } ]

let t_remove_ev rm = prove_by (rremove_ev rm)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Core rules: Bound probability directly} *)
(*i ----------------------------------------------------------------------- i*)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Admit proof obligation} *)

let radmit s _g = Radmit s, []
let t_admit s = prove_by (radmit s)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Distinguishability judgments are symmetric} *)

let rdist_sym ju =
  match ju.ju_pr with
  | Pr_Dist se' ->
    Rdist_sym, [ { ju_se = se'; ju_pr = Pr_Dist ju.ju_se } ]
  | _ ->
    tacerror "dist_sym: Dist judgment expected"

let t_dist_sym = prove_by rdist_sym

(*i ----------------------------------------------------------------------- i*)
(** {\bf Equal experiments cannot be distinguished} *)

let rdist_eq ju =
  let rn = "rdist_eq" in
  match ju.ju_pr with
  | Pr_Dist se' ->
    let se = ju.ju_se in
    ensure_gdef_eq  rn se.se_gdef se'.se_gdef;
    ensure_event_eq rn se.se_ev   se'.se_ev;
    Rdist_eq, []
  | _ ->
    tacerror "dist_eq: Dist judgment expected"

let t_dist_eq = prove_by rdist_eq

(*i ----------------------------------------------------------------------- i*)
(** {\bf Bound false event} *)

let rfalse_ev ju =
  ensure_pr_Succ_or_Adv "ctxt_ev" ju;
  if is_False ju.ju_se.se_ev.ev_expr
  then Rfalse_ev, []
  else tacerror "false_ev: event false expected"

let t_false_ev = prove_by rfalse_ev

(*i ----------------------------------------------------------------------- i*)
(** {\bf Bound random independence} *)

let check_event r ev =
  if ev.ev_binding <> [] 
     then tacerror "indep: the event can not be quantified";
  let ev = ev.ev_expr in
  let r = mk_V r in
  let rec aux i evs =
    match evs with
    | [] ->
      tacerror "indep: can not apply for variable %a and event@\  %a@\n"
        pp_exp r pp_exp ev
    | ev::evs ->
      let test_eq e1 e2 = e_equal e1 r && not (Se.mem r (e_vars e2)) in
      let check_eq e1 e2 =
        if test_eq e1 e2 then
          Rrnd_indep(true, i)
        else if test_eq e2 e1 then
          Rrnd_indep(false,i)
        else raise Not_found
      in
      try
        if is_Eq ev then
          let e1, e2 = destr_Eq ev in
          check_eq e1 e2
        (*
        else if is_Exists ev then
          let e1,e2,_ = destr_Exists ev in
          check_eq e1 e2
        *)
        else aux (i+1) evs
      with Not_found -> aux (i+1) evs
  in
  aux 0 (destr_Land_nofail ev)

let rrandom_indep ju =
  let se = ju.ju_se in
  match L.rev se.se_gdef with
  | GSamp(r,_)::_ ->
    if ty_equal r.Vsym.ty mk_Bool then ensure_pr_Adv "indep" ju;
    check_event r se.se_ev, []
  | _             -> tacerror "indep: the last instruction is not a random"

let t_random_indep = prove_by rrandom_indep

(*i ----------------------------------------------------------------------- i*)
(** {\bf Apply computational assumption} *)

let pp_range fmt (i,j) =
  F.fprintf fmt "%i - %i" i j

let ensure_ranges_cover_gdef rn rngs0 pref_len gdef =
  let gdef_len = L.length gdef in
  let rec go covered_upto rngs =
    match rngs with
    | [] ->
      if covered_upto <> gdef_len then
        tacerror "%s: ranges %a cover only up to to line %i, must cover up to %i"
          rn
          (pp_list "," pp_range) rngs0
          covered_upto gdef_len
    | (i,j)::rngs ->
      if i = covered_upto then go (j + 1) rngs
      else
        tacerror "%s: start %i of range should be %i" rn i covered_upto
  in
  go pref_len rngs0

let ensure_res_lets rn vres cres =
  assert (L.length vres = L.length cres);
  L.iter2
    (fun vs c ->
      match c with
      | GLet(vs',_) when Vsym.equal vs' vs -> ()
      | _ -> tacerror "%s: result binding not found for %a" rn Vsym.pp vs)
    vres cres

let assm_comp_valid_ranges rn assm acalls_ju rngs =
  let pref = assm.ac_prefix in
  let pref_len = L.length pref in
  let priv_vars = private_vars_comp assm in
  let rec go rngs acalls =
    match rngs, acalls with
    | [], [] -> ()
    | _::_, [] |  [], _::_ ->
      tacerror "%s: ranges and adversary calls do not match up" rn
    | (i,j)::rngs, (_,vres,e)::acalls ->
      let len = j - i + 1 in
      let len_res = L.length vres in
      let len_body = len - 1 - len_res in
      let acalls_ju = Util.drop (i - pref_len) acalls_ju in
      let c_arg  = L.hd acalls_ju in
      let c_body = Util.take len_body (Util.drop 1 acalls_ju) in
      let c_res  = Util.take len_res (Util.drop (1 + len_body) acalls_ju) in
      let read = read_gcmds (c_body@c_res) in
      ensure_not_use rn read priv_vars (c_body@c_res);
      if not assm.ac_inf then ensure_ppt rn (c_body@c_res);
      ensure_res_lets rn vres c_res;
      (* check and replace argument for adversary call *)
      (match c_arg with
       | GLet (_, e_arg) when (e_equal e_arg e) -> ()
       | GLet (_, e_arg) ->
         tacerror "%s: expected argument %a, got %a" rn
           pp_exp e_arg pp_exp e
       | _ ->
         tacerror "%s: range must start with let" rn);
      go rngs acalls
  in
  go rngs assm.ac_acalls

let rassm_comp assm0 rngs ren ju =
  let rname = "assumption_computational" in
  let se = ju.ju_se in
  let assm = Assumption.inst_comp ren assm0 in
  if assm.ac_type = A_Adv then ensure_pr_Adv rname ju;
  if assm.ac_type = A_Succ then ensure_pr_Succ_or_Adv rname ju;
  let pref = assm.ac_prefix in
  let pref_len = L.length pref in
  let pref_ju = Util.take pref_len se.se_gdef in
  let acalls_ju = Util.drop pref_len se.se_gdef in
  ensure_ren_inj rname ren;
  ensure_gdef_eq rname pref pref_ju;
  ensure_event_eq rname se.se_ev assm.ac_event;
  ensure_ranges_cover_gdef rname rngs (L.length pref_ju) se.se_gdef;
  (* check that we can instantiate calls in assumption with remainder of ju *)
  assm_comp_valid_ranges rname assm acalls_ju rngs;
  Rassm_comp(rngs,ren,assm0), []

let t_assm_comp assm ev_e subst = prove_by (rassm_comp assm ev_e subst)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Core rules: Rules with computationally bounded loss} *)
(*i ----------------------------------------------------------------------- i*)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Apply decisional assumption} *)
 
let assm_dec_valid_ranges rn dir assm acalls_ju rngs =
  let swap_dir = if dir = LeftToRight then id else Util.swap in  
  let (pref,_) = swap_dir (assm.ad_prefix1,assm.ad_prefix2) in
  let pref_len = L.length pref in
  let priv_vars = private_vars_dec assm in
  let rec go rngs acalls acalls_new =
    match rngs, acalls with
    | [], [] -> acalls_new
    | (i,j)::rngs, (_,vres,(e1,e2))::acalls ->
      let e_old,e_new = swap_dir (e1,e2) in
      let len = j - i + 1 in
      let len_res = L.length vres in
      let len_body = len - 1 - len_res in
      let acalls_ju = Util.drop (i - pref_len) acalls_ju in
      let c_arg  = L.hd acalls_ju in
      let c_body = Util.take len_body (Util.drop 1 acalls_ju) in
      let c_res  = Util.take len_res  (Util.drop (1 + len_body) acalls_ju) in
      let read = read_gcmds (c_body@c_res) in
      ensure_not_use rn read priv_vars (c_body@c_res);
      ensure_ppt rn (c_body@c_res);
      if not assm.ad_inf then ensure_ppt rn (c_body@c_res);
      ensure_res_lets rn vres c_res;
      let v_arg = 
        match c_arg with
        | GLet (v_arg, e_arg) when (e_equal e_arg e_old) -> v_arg
        | GLet (_, e_arg) ->
          tacerror "%s: expected argument %a, got %a"
            rn pp_exp e_old pp_exp e_arg
        | _ -> tacerror "%s: expected let in first line of range" rn
      in
      go rngs acalls (acalls_new@[GLet(v_arg,e_new)]@c_body@c_res)
    | _, _ -> tacerror "%s: ranges and adversary calls do not match up" rn
  in
  go rngs assm.ad_acalls []
  
let rassm_dec dir ren rngs assm0 ju =
  let rn = "assumption_decisional" in
  let se = ju.ju_se in
  let swap_dir = if dir = LeftToRight then id else Util.swap in
  (* check that prefix of (renamed) assumption coincides with prefix of ju *)
  let assm = Assumption.inst_dec ren assm0 in
  let pref_old,pref_new = swap_dir (assm.ad_prefix1,assm.ad_prefix2) in
  let pref_old_len = L.length pref_old in
  let pref_ju = Util.take pref_old_len se.se_gdef in
  let acalls_ju = Util.drop pref_old_len se.se_gdef in
  ensure_ren_inj rn ren;
  ensure_gdef_eq rn pref_ju pref_old;
  (* check that event is equal to last returned variable *)
  let ev_is_last_returned = 
    match Util.last acalls_ju with
    | GLet(vs,_) when e_equal se.se_ev.ev_expr (mk_V vs) &&
                      se.se_ev.ev_binding = []         -> true
    | _                                                -> false
  in
  if not ev_is_last_returned then
    tacerror "assm_dec: event must be equal to variable defined in last line";
  ensure_ranges_cover_gdef rn rngs (L.length pref_ju) se.se_gdef;
  (* check that we can instantiate calls in assumption with remainder of ju *)
  let acalls_ju_new = assm_dec_valid_ranges rn dir assm acalls_ju rngs in
  let se = { se with se_gdef = pref_new@acalls_ju_new } in
  Rassm_dec(rngs,dir,ren,assm0), [{ ju with ju_se = se }]

let t_assm_dec dir ren rngs assm = prove_by (rassm_dec dir ren rngs assm)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Add a new test to oracle.} *)

let radd_test opos tnew asym fvs ju =
  let se = ju.ju_se in
  match get_se_octxt se opos with
  | LGuard(t), seoc ->
    assert (ty_equal tnew.e_ty mk_Bool);
    let destr_guard lcmd =
      match lcmd with
      | LGuard(e) -> e
      | _ -> tacerror "add_test: new test cannot be inserted after %a, %s"
               (pp_lcmd ~qual:Unqual) lcmd "preceeding commands must be tests"
    in
    let tests = L.map destr_guard (L.rev seoc.seoc_cleft) in
    let subst =
      L.fold_left2
        (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
        Me.empty seoc.seoc_oargs fvs
    in
    let seoc = { seoc with seoc_cleft = LGuard(tnew) :: seoc.seoc_cleft } in
    let seoc_bad =
      { seoc with
        seoc_asym = asym;
        seoc_avars = fvs;
        seoc_sec =
          { seoc.seoc_sec with
            sec_ev = 
              { ev_quant = Forall;
                ev_binding = [];
                ev_expr = e_subst subst (mk_Land (tests@[ t ; mk_Not tnew]))};
            sec_right = [] } }
    in
    let ju1 = {ju_se = set_se_octxt [LGuard(t)] seoc_bad; ju_pr = Pr_Succ } in
    let ju2 = { ju with ju_se =  set_se_octxt [LGuard(t)] seoc } in
    Radd_test(opos, tnew, asym, fvs), [ ju1; ju2 ]
  | _ -> tacerror "add_test: given position is not a test"

let t_add_test p tnew asym fvs = prove_by (radd_test p tnew asym fvs)

(*i ----------------------------------------------------------------------- i*)
(** {\bf Transitivity: bound distance to given intermediate game.} *)

let rtrans new_se ju =
  wf_se NoCheckDivZero new_se;
  let se = ju.ju_se in
  let ju1 = { ju_se = se; ju_pr = Pr_Dist new_se } in
  let ju2 = { ju_se = new_se; ju_pr = ju.ju_pr } in
  Rtrans, [ ju1; ju2 ]

let t_trans new_se =
  prove_by (rtrans new_se)


(*i ----------------------------------------------------------------------- i*)
(** {\bf Hybrid argument.} *)

let rename_odef lcmds ret =
  let vmap = Vsym.H.create 134 in
  let add_mapping lcmd =
    match lcmd with
    | LLet(v,_) | LSamp(v,_) ->
      let id = v.Vsym.id in
      let new_v = Vsym.mk (Id.name id) v.Vsym.ty in
      Vsym.H.add vmap v new_v
    | LGuard(_) -> ()
    | LBind(_) -> assert false
  in
  L.iter add_mapping lcmds;
  let sigma v = try Vsym.H.find vmap v with Not_found -> v in
  (L.map (subst_v_lc sigma) lcmds, subst_v_e sigma ret)

let rhybrid gpos oidx new_lcmds new_eret ju =
  let se = ju.ju_se in
  let _, seoc = get_se_octxt_len se (gpos,oidx,0,Onohyb) 0 in
  let old_lcmds = seoc.seoc_cright in
  let old_ret = seoc.seoc_return in
  (* replace oracle definition in second judgment *)
  let ju2  =
    { ju with
      ju_se = 
        set_se_octxt []
          { seoc with
            seoc_return = new_eret;
            seoc_cright = new_lcmds } }
  in
  let ev = ju.ju_se.se_ev in
  assert (ev.ev_binding = []);
  let splitEv =
    let conj = destr_Land_nofail ev.ev_expr in
    conc_map
      (fun e ->
        if is_All e then (
          match destr_All e with
          | [(vs,o)],e1 when Osym.equal o seoc.seoc_osym ->
            [e; e_subst (L.fold_left2
                           (fun m e1 e2 -> Me.add (mk_V e1) (mk_V e2) m)
                           Me.empty vs seoc.seoc_oargs) e1]
          | _ -> [e]
        ) else (
          [e]
        ) 
      )
      conj
  in
  (* use hybrid oracles in first judgment *)
  let seoc_left1 =
    { seoc with
      seoc_sec =
        { seoc.seoc_sec with
          sec_ev = { ev_binding = []; ev_quant = Forall; ev_expr = mk_Land splitEv } };
      seoc_obless    = Some (rename_odef new_lcmds new_eret);
      seoc_obeq      = None;
      seoc_cright    = old_lcmds;
      seoc_return    = old_ret;
      seoc_obgreater = Some (rename_odef old_lcmds old_ret); }
  in
  let seoc_left2 =
    { seoc_left1 with
      seoc_return = new_eret;
      seoc_cright = new_lcmds; }
  in
  let ju1 =
    { ju_se = set_se_octxt [] seoc_left1;
      ju_pr = Pr_Dist (set_se_octxt [] seoc_left2);
    }
  in
  Rhybrid, [ ju1; ju2 ]

let t_hybrid gpos oidx lcmds eret =
  prove_by (rhybrid gpos oidx lcmds eret)


let rguard opos tnew ju =
  let se = ju.ju_se in
  let seoc,t = 
    match tnew with
    | None ->
      begin match get_se_octxt se opos with
      | (LGuard(t), seoc) -> seoc, t 
      | _ -> tacerror "guard: given position is not a test"
      end
   | Some t ->
      snd (get_se_octxt_len se opos 0), t in

  assert (ty_equal t.e_ty mk_Bool);
  let destr_guard lcmd =
    match lcmd with
    | LGuard(e) -> e
    | _ -> tacerror "add_test: new test cannot be inserted after %a, %s"
      (pp_lcmd ~qual:Unqual) lcmd "preceeding commands must be tests"
  in
  let vs = 
    List.map (fun v -> Vsym.mk (Vsym.to_string v) v.Vsym.ty) seoc.seoc_oargs
  in
    
  let tests = L.map destr_guard (L.rev seoc.seoc_cleft) in
  let subst =
    L.fold_left2
      (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
      Me.empty seoc.seoc_oargs vs
  in

  (* bad event *)
  let seoc_bad = 
    { seoc with 
      seoc_sec = { seoc.seoc_sec with 
        sec_right = [];
        sec_ev = 
          { ev_quant = Exists;
            ev_binding = [vs,seoc.seoc_osym];
            ev_expr = e_subst subst (mk_Land (mk_Not t::tests))}
      }} in
  let i = if tnew = None then [] else [LGuard t] in
  let ju1 = {ju_se = set_se_octxt i seoc_bad; ju_pr = Pr_Succ } in
  let ju2 = {ju with ju_se = set_se_octxt i seoc } in
  Wf.wf_se NoCheckDivZero ju1.ju_se;
  Wf.wf_se NoCheckDivZero ju2.ju_se;
  Rguard(opos, tnew), [ ju1; ju2 ]

let t_guard p tnew = prove_by (rguard p tnew)

let rguess asym fvs ju = 
  let ev = ju.ju_se.se_ev in
  match ev.ev_quant, ev.ev_binding, ju.ju_pr with
  | Exists, [vs,_o], Pr_Succ ->
    assert (ty_equal (ty_prod_vs fvs) (ty_prod_vs vs));
    let subst =
      L.fold_left2
        (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
        Me.empty vs fvs in
    let e = e_subst subst ev.ev_expr in
    let ju1 = {ju with
      ju_se = {
        se_gdef = ju.ju_se.se_gdef @ [GCall(fvs,asym,mk_Tuple [], [])];
        se_ev = { ev_quant = Forall; ev_binding = []; ev_expr = e }} } in
    Wf.wf_se NoCheckDivZero ju1.ju_se;
    Rguess asym, [ ju1 ]
    
  | _ ->
    tacerror "guess: not a valid event"

let t_guess asym fvs = prove_by (rguess asym fvs)

let rfind (bd,body) arg asym fvs ju =
  let ev = ju.ju_se.se_ev in
  match ev.ev_quant, ev.ev_binding, ju.ju_pr with
  | Exists, [vs,_o], Pr_Succ ->
    assert (ty_equal (ty_prod_vs fvs) (ty_prod_vs vs));
    (* check that body{bd <- arg} = ev.ev_expr *)
    assert (ty_equal (ty_prod_vs bd) arg.e_ty);
    let subst_bd = 
      L.fold_left2 (fun s v e -> Me.add (mk_V v) e s) Me.empty bd 
        (if L.length bd > 1 then destr_Tuple_nofail arg else [arg]) in
    let fv = e_vars body in
    let se_vs = List.fold_left (fun s v -> Se.add (mk_V v) s) Se.empty in
    let allowed = Se.union (se_vs vs) (se_vs bd) in
    if not (Se.subset fv allowed) then
      tacerror "find not a closed function: %a contains variables not in %a"
        pp_exp body (pp_list "," pp_exp) (Se.elements allowed);
    let e1 = e_subst subst_bd body in
    if not (e_equal e1 ev.ev_expr) then
      tacerror "find: invalid function or argument: %a vs %a" pp_exp e1 pp_exp ev.ev_expr;
    (* check that the function is PPT *)
    if not (is_ppt body) then 
      tacerror "find: the function is not ppt";
    (* build the game *)
    let subst =
      L.fold_left2
        (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
        Me.empty vs fvs in
    let e = e_subst subst ev.ev_expr in
    let ju1 = {ju with
      ju_se = {
        se_gdef = ju.ju_se.se_gdef @ [GCall(fvs,asym,arg, [])];
        se_ev = { ev_quant = Forall; ev_binding = []; ev_expr = e }} } in
    Wf.wf_se NoCheckDivZero ju1.ju_se;
    Rfind (asym, (bd,body)), [ ju1 ]
    
  | _ ->
    tacerror "find: not a valid event"

let t_find f arg asym fvs = prove_by (rfind f arg asym fvs)
  
