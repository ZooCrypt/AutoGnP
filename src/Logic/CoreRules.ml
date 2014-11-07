(*s Core rules of the logic. *)

(*i*)
open Abbrevs
open Util
open Nondet
open Type
open Expr
open ExprUtils
open Game
open Wf
open Assumption
open Syms
open CoreTypes

let log_t ls = mk_logger "Logic.Core" Bolt.Level.TRACE "CoreRules" ls
let log_d ls = mk_logger "Logic.Core" Bolt.Level.DEBUG "CoreRules" ls
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Types for proofs and tactics} *)

(** Proof tree. *)
type proof_tree = {
  pt_children : proof_tree list;
  pt_rule     : rule_name;
  pt_ju       : judgment
}

let pt_replace_children pt pts =
  let equal_fact pt1 pt2 = ju_equal pt1.pt_ju pt2.pt_ju in
  assert (Util.list_eq_for_all2 equal_fact pt.pt_children pts);
  { pt with pt_children = pts }

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
type 'a rtactic = goal -> ('a * proof_state) nondet

let mk_name se =
  let vars = gdef_all_vars se.se_gdef in
  let name_of_int i = "r"^(string_of_int i) in
  let names =
    Vsym.S.fold (fun vs se -> Sstring.add (Id.name vs.Vsym.id) se) vars Sstring.empty
  in
  let rec go n =
    let name = name_of_int n in
    if Sstring.mem name  names then go (n+1) else name
  in
  go 1

(*i ----------------------------------------------------------------------- i*)
(* \hd{General purpose functions} *)

(** Raised if there is no open goal. *)
exception NoOpenGoal

(** Fail with message [s] if variable [vs] occurs in [ju]. *)
let _fail_if_occur vs se s =
  if (Vsym.S.mem vs (gdef_all_vars se.se_gdef)) then
    tacerror "%s: variable %a occurs in judgment\n %a" s Vsym.pp vs pp_se se

(** Prove goal [g] by rule [ru] which yields [subgoals]. *)
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
          }
      }
  with
    Invalid_rule s ->
      mfail s

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
  { subgoals   = L.flatten (L.map (fun gs -> gs.subgoals) pss);
    validation = validation' [] pss }

(*i ----------------------------------------------------------------------- i*)
(* \hd{Tacticals and goal management} *)

(** Tactic that moves the first subgoal to the last position. *)
let move_first_last ps =
  match ps.subgoals with
  | [] -> tacerror "last: no goals"
  | ju :: jus ->
    let validation pts =
      match L.rev pts with
      | pt :: pts -> ps.validation (pt::L.rev pts)
      | _ -> assert false in
    { subgoals = jus @ [ju];
      validation = validation }

(** Apply the tactic [t] to the [n]-th subgoal of proof state [ps]. *)
let apply_on_n n t ps =
  let len = L.length ps.subgoals in
  if len = 0 then raise NoOpenGoal;
  if len <= n then tacerror "there is only %i subgoals" len;
  let hd, g, tl =
    Util.split_n n ps.subgoals
  in
  t g >>= fun gsn ->
  let vali pts =
    let hd, tl = Util.cut_n n pts in
    let ptn, tl = Util.cut_n (L.length gsn.subgoals) tl in
    ps.validation (L.rev_append hd (gsn.validation (L.rev ptn) :: tl))
  in
  ret { subgoals = L.rev_append hd (gsn.subgoals @ tl);
        validation = vali }

(** Apply the tactic [t] to the first subgoal in proof state [ps]. *)
let apply_first t ps = apply_on_n 0 t ps

(** Identity tactic. *)
let t_id g = ret (
  { subgoals = [g];
    validation = fun pts -> match pts with [pt] -> pt | _ -> assert false })

let t_bind_ignore (t1 : 'a rtactic) (ft2 : 'a -> tactic) g =
  t1 g >>= fun (x,ps1) ->
  mapM (ft2 x) ps1.subgoals >>= fun ps2s ->
  ret (merge_proof_states ps2s ps1.validation)

let t_cut t g =
  let pss = t g in
  match pull pss with
  | Left(Some s) -> mfail s
  | Left None    -> mfail "t_cut: mempty"
  | Right(x,_)   -> ret x

(** Apply [t1] to goal [g] and [t2] to all resulting subgoals. *)
let t_bind (t1 : 'a rtactic) (ft2 : 'a -> 'b rtactic) g =
  t1 g >>= fun (x,ps1) ->
  mapM (ft2 x) ps1.subgoals >>= fun ps2s ->
  match ps2s with
  | [y,ps2] ->
    ret (y,merge_proof_states [ps2] ps1.validation)
  | _ ->
    mfail "t_bind: expected exactly one goal"

let apply_all t ps =
  mapM t ps.subgoals >>= fun pss ->
  ret (merge_proof_states pss ps.validation)

let rapply_all rt ps =
  mapM rt ps.subgoals >>= fun pss ->
  match pss with
  | [y,ps2] ->
    ret (y,merge_proof_states [ps2] ps.validation)
  | _ ->
    mfail "t_bind: expected exactly one goal"

let t_seq_list t1 t2s g =
  t1 g >>= fun ps1 ->
  assert (L.length t2s = L.length ps1.subgoals);
  mapM (fun (t2,g) -> t2 g) (L.combine t2s ps1.subgoals) >>= fun ps2s ->
  ret (merge_proof_states ps2s ps1.validation)

let t_seq t1 t2 g =
  t1 g >>= fun ps1 ->
  mapM t2 ps1.subgoals >>= fun ps2s ->
  ret (merge_proof_states ps2s ps1.validation)

let t_ensure_progress t g =
  t g >>= fun ps ->
  guard (ps.subgoals <> [g]) >>= fun _ ->
  ret ps

(** Apply tactic [t1] to goal [g] or [t2] in case of failure. *)
let t_or tn1 tn2 g = Nondet.mplus (tn1 g)  (tn2 g)

(** Apply tactic [t] or [t_id] in case of failure. *)
let t_try t g = t_or t t_id g

(** Failure, takes a format string *)
let t_fail fs _g =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      log_t (lazy s);
      mfail s)
    fbuf fs

(*i ----------------------------------------------------------------------- i*)
(* \hd{Rules for main (equivalence/small statistical distance)} *)

(** Conversion. *)

(** [rconv do_norm new_se se] takes a boolean that
    determines if both judgments have to be normalized,
    then it checks that [se] is equal to [new_se] after
    normalizing and comparing the two judgments *)
let rconv do_norm_terms ?do_rename:(do_rename=false) new_se ju =
  let se = ju.ju_se in
  let (nf,ctype) =
    if do_norm_terms
    then (Norm.norm_expr_strong,CheckDivZero)
    else (id,NoCheckDivZero)
  in
  wf_se ctype se;
  wf_se ctype new_se;
  let se' = norm_se ~norm:nf se in
  let new_se' = norm_se ~norm:nf new_se in
  let se' =
    if do_rename then
      try
        let sigma = Game.unif_se se' new_se' in
        if not (Game.ren_injective sigma) then
          tacerror "rconv: computed renaming is not bijective";
        norm_se ~norm:nf (subst_v_se (fun vs -> Vsym.M.find vs sigma) se')
      with
        Not_found ->
          log_t (lazy "no renaming found");
          se'
    else
      se'
  in
  if not (se_equal se' new_se') then
    tacerror "rconv: not convertible@\n %a@\n %a" pp_se se' pp_se new_se';
  log_d (lazy (fsprintf "!!! conv rule applied"));
  Rconv, [{ ju with ju_se = new_se }]

let t_conv do_norm_terms ?do_rename:(do_rename=false) new_se =
  prove_by (rconv do_norm_terms ~do_rename new_se)

(** Swap instruction. *)

let disjoint s1 s2 = Se.is_empty (Se.inter s1 s2)

let check_swap read write i c =
  let i = [i] in
  let ir = read i in
  let iw = write i in
  let cr = read c in
  let cw = write c in
  if not (disjoint iw cw && disjoint ir cw && disjoint cr iw)
  then tacerror "swap : can not swap"

let swap i delta ju =
  if delta = 0 then ju
  else
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
    check_swap read_gcmds write_gcmds instr c2;
    if is_call instr && has_call c2
    then tacerror "swap : can not swap";
    let c2,c3 = if delta > 0 then c2, instr::c3 else instr::c2, c3 in
    log_d (lazy (fsprintf "!!! swap rule applied: i=%i delta=%i" i delta));
    { ju with ju_se = set_se_ctxt c2 {sec_left=c1; sec_right=c3; sec_ev=e} }

let rswap i delta ju = Rswap(i, delta), [swap i delta ju]

let t_swap i delta = prove_by (rswap i delta)

(** Random rule. *)

let ensure_bijection c1 c2 v =
  if not (Norm.e_equalmod (inst_ctxt c2 (inst_ctxt c1 v)) v &&
          Norm.e_equalmod (inst_ctxt c1 (inst_ctxt c2 v)) v)
  then tacerror "random: contexts not bijective"

(*i 'random p c1 c2' takes a position p and two contexts.
    It first ensures that there is a random sampling 'x <-$ d' at position p.
    For now, excepted distributions are not allowed.
    Then it checks that c1 and c2 are well-formed for at position p
    (taking inequalities that are checked beforehand into account)
    and that 'forall x in supp(d), c2(c1(x)) = x /\ c1(c2(x)) = x'.  i*)
let rrnd p c1 c2 ju =
  let se = ju.ju_se in
  match get_se_ctxt se p with
  | GSamp(vs,((_t,[]) as d)), sec ->
    let v = mk_V vs in
    ensure_bijection c1 c2 v;
    let vslet = Vsym.mk (mk_name se) vs.Vsym.ty in
    let cmds =
      [ GSamp(vs,d);
        GLet(vslet, inst_ctxt c1 (mk_V vs)) ]
    in
    let wfs = wf_gdef NoCheckDivZero (L.rev sec.sec_left) in
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c1)) (snd c1);
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c2)) (snd c2);
    let subst e = e_replace v (mk_V vslet) e in
    let sec =
      { sec with
        sec_right = map_gdef_exp subst sec.sec_right;
        sec_ev    = subst sec.sec_ev }
    in
    log_d (lazy (fsprintf "!!! rrnd applied at %i for %a" p Vsym.pp vs));
    Rrnd(p,vs,c1,c2), [ { ju with ju_se = set_se_ctxt cmds sec } ]
  | _ -> tacerror "rrnd: position given is not a sampling"

let t_rnd p c1 c2 = prove_by (rrnd p c1 c2)

(** Exclude from sampling. *)

let rexcept p es ju =
  let se = ju.ju_se in
  match get_se_ctxt se p with
  | GSamp(_,(_,es')), _ when list_equal e_equal es' es ->
    tacerror "rexcept: identical exceptions already present"    
  | GSamp(vs,(t,_)), sec ->
    log_d (lazy (fsprintf "!!! except applied: %a" (pp_list "," pp_exp) es));
    Rexc(p, es), [ {ju with ju_se = set_se_ctxt [ GSamp(vs,(t,es)) ] sec} ]
  | _ ->
    tacerror "rexcept: position given is not a sampling"

let t_except p es = prove_by (rexcept p es)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Rules for oracle (equivalence/small statistical distance)} *)

(** Rewrite oracle using test. *)

let rrewrite_oracle op dir ju =
  let se = ju.ju_se in
  match get_se_octxt se op with
  | LGuard(t) as lc, seoc ->
    (* replace a by b *)
    let (a,b) = match t.e_node with
      | App(Eq,[u;v]) ->
        if dir = LeftToRight then (u,v) else (v,u)
      | _ -> assert false
    in
    let subst e = e_replace a b e in
    let seoc = { seoc with
                 seoc_cright = L.map (map_lcmd_exp subst) seoc.seoc_cright;
                 seoc_return = subst seoc.seoc_return }
    in
    let (i,j,k) = op in
    log_d (lazy (fsprintf "!!! rrw_oracle %i,%i,%i @\n" i j k));
    Rrw_orcl(op,dir), [ { ju with ju_se = set_se_octxt [lc] seoc } ]
  | _ -> assert false

let t_rewrite_oracle op dir = prove_by (rrewrite_oracle op dir)

(** Swap instruction. *)

let swap_oracle i delta ju =
  if delta = 0 then ju
  else
    let se = ju.ju_se in
    let i, seoc = get_se_octxt se i in
    let c1_rev,c2,c3 =
      if delta < 0 then
        let hhd,thd = cut_n (-delta) seoc.seoc_cleft in
        thd,hhd,seoc.seoc_cright
      else
        let htl, ttl = cut_n delta seoc.seoc_cright in
        seoc.seoc_cleft, L.rev htl, ttl in
    check_swap read_lcmds write_lcmds i c2;
    let c2, c3 =
      if delta > 0 then c2, i::c3 else i::c2, c3 in
    { ju with ju_se = set_se_octxt c2 { seoc with seoc_cleft = c1_rev; seoc_cright = c3 } }

let rswap_oracle i delta ju =
  Rswap_orcl(i,delta), [swap_oracle i delta ju]

let t_swap_oracle i delta = prove_by (rswap_oracle i delta)

(** Random rule. *)

let rrnd_oracle p c1 c2 ju =
  let se = ju.ju_se in
  match get_se_octxt se p with
  | LSamp(vs,((_t,[]) as d)), juoc ->
    let v = mk_V vs in
    ensure_bijection c1 c2 v;
    let cmds = [ LSamp(vs,d);
                 LLet(vs, inst_ctxt c1 (mk_V vs)) ]
    in
    (* ensure both contexts well-defined *)
    let wfs = wf_gdef CheckDivZero (L.rev juoc.seoc_sec.sec_left) in
    let wfs = ensure_varnames_fresh wfs juoc.seoc_oargs in
    let wfs = wf_lcmds CheckDivZero wfs (L.rev juoc.seoc_cleft) in
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c1)) (snd c1);
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c2)) (snd c2);
    let juoc = { juoc with
                 seoc_return = juoc.seoc_return;
                 seoc_cright = juoc.seoc_cright }
    in
    let (i,j,k) = p in
    log_d (lazy
      (fsprintf "!!! rrnd_oracle applied at (%i,%i,%i) for %a" i j k Vsym.pp vs));
    Rrnd_orcl(p,c1,c2), [ { ju with ju_se = set_se_octxt cmds juoc } ]
  | _ -> tacerror "random: position given is not a sampling"

let t_rnd_oracle p c1 c2 = prove_by (rrnd_oracle p c1 c2)

(** Exclude values from sampling. *)

let rexcept_oracle p es ju =
  let se = ju.ju_se in
  match get_se_octxt se p with
  | LSamp(vs,(t,_es)), seoc ->
    Rexc_orcl(p,es), [ { ju with ju_se = set_se_octxt [ LSamp(vs,(t,es)) ] seoc } ]
  | _ -> tacerror "rexcept_oracle: position given is not a sampling"

let t_except_oracle p es = prove_by (rexcept_oracle p es)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Rules for case distinctions and up-to} *)

(** Perform case distinction on event. *)

let rcase_ev ?flip:(flip=false) e ju =
  (*i FIXME: think about allowed ju_pr and ju_pr of result i*)
  let se = ju.ju_se in
  let ev = se.se_ev in
  let se1 = { se with se_ev = mk_Land [ev;e] } in
  let se2 = { se with se_ev = mk_Land [ev; (mk_Not e)] } in
  if is_Land ev &&
    let evs = L.map Norm.norm_expr_weak (destr_Land ev) in
    (L.mem (Norm.norm_expr_weak e) evs || L.mem (Norm.norm_expr_weak (mk_Not e)) evs)
  then tacerror "rcase_ev: event or negation already in event";
  log_d (lazy (fsprintf "!!! case_ev rule applied: %a" pp_exp e));
  let ju1 = { ju with ju_se = se1 } in
  let ju2 = { ju with ju_se = se2 } in  
  Rcase_ev(flip, e), if flip then [ju2; ju1] else [ju1;ju2]

let t_case_ev ?flip:(flip=false) e = prove_by (rcase_ev ~flip e)

(** Up-to bad: add new test to oracle.\\
   We get two new judgments for $G : E$ after
   applying [radd_test (i,j,k) t' vz A]:
   \begin{itemize}
   \item $G' : E$ (where the test $t'$ is added to position $k$ of the oracle at $i,j$)
   \item $G'_{1..i}; vz \leftarrow A() : t \land t'$
     (where $t$ is the test in the oracle and $G'_{1..i}$ consist
      of the first $i$ lines of $G'$)
   \end{itemize}
*)
let radd_test opos tnew asym fvs ju =
  let se = ju.ju_se in
  match get_se_octxt se opos with
  | LGuard(t), seoc ->
    assert (ty_equal tnew.e_ty mk_Bool);
    let destr_guard lcmd =
      match lcmd with
      | LGuard(e) -> e
      | _ ->
        tacerror ("radd_test: new test cannot be inserted after %a, " ^^
                   "preceeding commands must be tests")
             pp_lcmd lcmd
    in
    let tests = L.map destr_guard (L.rev seoc.seoc_cleft) in
    let subst =
      L.fold_left2
        (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
        Me.empty seoc.seoc_oargs fvs
    in
    let seoc =
      { seoc with
        seoc_cleft = LGuard(tnew) :: seoc.seoc_cleft }
    in
    log_d (lazy (fsprintf "!!! add_test rule applied: %a" pp_exp tnew));
    let ju1 =
      {ju_se = 
         set_se_octxt [ LGuard(t) ]
          { seoc with
            seoc_asym = asym;
            seoc_avars = fvs;
            seoc_sec =
              { seoc.seoc_sec with
                sec_ev = e_subst subst (mk_Land (tests@[ t ; mk_Not tnew]));
                sec_right = []
              }
          };
       ju_pr = Pr_Succ
      }
    in
    let ju2 = { ju with ju_se =  set_se_octxt [ LGuard(t) ] seoc } in
    Radd_test(opos, tnew, asym, fvs), [ ju1; ju2 ]
  | _ -> tacerror "radd_test: given position is not a test"

let t_add_test p tnew asym fvs = prove_by (radd_test p tnew asym fvs)

(** Bad rule for random oracle. *)

let rbad _p _vsx _ju =
  failwith "undefined"
  (*i
  fail_if_occur vsx se "rbad";
  match get_se_ctxt se p with
  | GLet(vs,e'), ctxt when is_H e' ->
    let h,e = destr_H e' in
    if not (Hsym.is_ro h) then
      tacerror "the function %a is not a random oracle" Hsym.pp h;
    (*i FIXME: check that h is only used here and that calls are guarded in oracle i*)
    let i = [GSamp(vs,(e'.e_ty,[]))] in
    let se1 = set_se_ctxt i ctxt in
    let vx = mk_V vsx in
    let ev = mk_Exists e vx [vsx,h] in
    let se2 = { se1 with se_ev = ev } in
    Rbad(p,vsx), [se1;se2]
  | _ ->
    tacerror "can not apply bad rule"
  i*)

let t_bad p vsx = prove_by (rbad p vsx)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Rules for implications between events} *)

(** Apply context to event. *)

let rctxt_ev i c ju =
  (*i FIXME: check for which ju_pr this should be allowed i*)
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev in
  if i < 0 || i >= L.length evs then failwith "invalid event position";
  let l,b,r = Util.split_n i evs in
  let b =
    if is_Eq b then
      let (e1,e2) = destr_Eq b in
      mk_Eq (inst_ctxt c e1) (inst_ctxt c e2)
    else if is_Exists b then
      let (e1,e2,h) = destr_Exists b in
      mk_Exists (inst_ctxt c e1) (inst_ctxt c e2) h
    else tacerror "rctxt_ev: bad event, expected equality or exists"
  in
  let ev = mk_Land (L.rev_append l (b::r)) in
  let wfs = wf_gdef NoCheckDivZero (se.se_gdef) in
  wf_exp CheckDivZero wfs ev;
  let new_ju = { se with se_ev = ev } in
  log_d 
    (lazy (fsprintf "!!! rctxt_ev applied at %i for %a -> %a@\n"
             i Vsym.pp (fst c) pp_exp (snd c)));
  Rctxt_ev(i, c), [ { ju with ju_se = new_ju } ]

let t_ctxt_ev i c = prove_by (rctxt_ev i c)

(** Remove events. *)

let rremove_ev (rm:int list) ju =
  (*i FIXME: check allowed ju_pr i*)
  let se = ju.ju_se in
  let rec aux i evs =
    match evs with
    | [] -> []
    | ev::evs ->
      let evs = aux (i+1) evs in
      if L.mem i rm then evs else ev::evs in
  let ev = se.se_ev in
  let evs = aux 0 (destr_Land_nofail ev) in
  let new_ju = {se with se_ev = if evs = [] then mk_True else mk_Land evs} in
  Rremove_ev rm, [ { ju with ju_se = new_ju } ]

let t_remove_ev rm = prove_by (rremove_ev rm)

(** Merge conjuncts in event. *)

let merge_base_event ev1 ev2 =
  match ev1.e_node, ev2.e_node with
  | App (Eq,[e11;e12]), App(Eq,[e21;e22]) ->
    mk_Eq (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22])
  | App (Eq,[e11;e12]), Exists(e21,e22, l) ->
    mk_Exists (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22]) l
  | Exists(e11,e12, l), App (Eq,[e21;e22]) ->
    mk_Exists (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22]) l
  | Exists(e11,e12, l1), Exists(e21,e22, l2) ->
    (*i FIXME we should be sure that bound variables in l1 and l2 are disjoint i*)
    mk_Exists (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22]) (l1 @ l2)
  | _, _ -> failwith "do not knwon how to merge the event"

let rmerge_ev i j ju =
  let se = ju.ju_se in
  let i,j = if i <= j then i, j else j, i in
  let evs = destr_Land_nofail se.se_ev in
  let l,b1,r = Util.split_n i evs in
  let l',b2,r =
    if i = j then [], b1, r
    else Util.split_n (j - i - 1) r in
  let ev = merge_base_event b1 b2 in
  let evs = L.rev_append l (L.rev_append l' (ev::r)) in
  let new_se = {se with se_ev = mk_Land evs} in
  Rmerge_ev(i,j), [ { ju with ju_se = new_se } ]

let t_merge_ev i j = prove_by (rmerge_ev i j)

(** Split equality on products into multiple equalities. *)

let rsplit_ev i ju =
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev in
  if i < 0 || i >= L.length evs then failwith "invalid event position";
  let l,b,r = Util.split_n i evs in
  let b =
    if not (is_Eq b)
      then tacerror "rsplit_ev: bad event, expected equality";
    let (e1,e2) = destr_Eq b in
    if not (is_Tuple e1 && is_Tuple e2)
      then tacerror "rsplit_ev: bad event, tuples";
    let es1, es2 = destr_Tuple e1, destr_Tuple e2 in
    if not (L.length es1 = L.length es2)
      then tacerror "rsplit_ev: bad event, tuples";
    L.map (fun (e1,e2) -> mk_Eq e1 e2) (L.combine es1 es2)
  in
  let evs = l@b@r in
  let new_se = {se with se_ev = mk_Land evs} in
  log_d (lazy (fsprintf "rsplit_ev %i" i));
  Rsplit_ev(i), [ { ju with ju_se = new_se } ]

let t_split_ev i = prove_by (rsplit_ev i)

(** Rewrite event with equality. *)

let rrw_ev i d ju =
  let se = ju.ju_se in
  let ev = se.se_ev in
  let evs = destr_Land_nofail ev in
  if i < 0 || i >= L.length evs then failwith "invalid event position";
  let l,b,r = Util.split_n i evs in
  let u,v =
    if is_Eq b then (
      let u,v = destr_Eq b in
      if d = LeftToRight then (u,v) else (v,u)
    ) else if is_Not b && is_Eq (destr_Not b) then (
      let eq = destr_Not b in
      if d = LeftToRight then (eq,mk_False)
      else tacerror "rrw_ev: inequality can only be used from left to right"
    ) else (
      tacerror "rrw_ev: bad event, expected equality"
    )
  in
  let subst e = e_replace u v e in
  let evs = (L.map subst l |> L.rev)@[b]@(L.map subst r) in
  let new_se = { se with se_ev = mk_Land evs } in
  log_d (lazy (fsprintf "rrw_ev %i" i));
  Rrw_ev(i,d), [ { ju with ju_se = new_se } ]

let t_rw_ev i d = prove_by (rrw_ev i d)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Rules for decisional and computational assumptions} *)

(** Reduction to decisional assumptions. *)

(* The renaming 'ren' must rename the random variables and the variables for
   return values in the assumption to match with variables in 'ju'.
   The ranges 'rngs' must be disjoint, cover everything except the sampling
   prefix, start with an assignment 'let argi = ei' and end with assignments
   to the return values of the adversary. Everything except 'ei' cannot use
   the random variables directly and must be ppt. *)
let rassm_dec dir ren rngs assm0 ju =
  let se = ju.ju_se in
  if not (ren_injective ren) then tacerror "assm_dec: renaming is not bijective";
  let swap_dir = if dir = LeftToRight then id else Util.swap in

  (* check that prefix of (renamed) assumption coincides with prefix of ju *)
  let assm = Assumption.inst_dec ren assm0 in
  let prefix_old,prefix_new = swap_dir (assm.ad_prefix1,assm.ad_prefix2) in
  let prefix_old_len = L.length prefix_old in
  let prefix_ju = Util.take prefix_old_len se.se_gdef in
  let acalls_ju = Util.drop prefix_old_len se.se_gdef in
  if not (gdef_equal prefix_old prefix_ju) then tacerror "assm_dec: prefixes not equal";

  log_d (lazy (fsprintf "rassm_dec, renamed assumption:@\n@[<hov 4>  %a@]"
                 pp_assm_dec assm));
  log_d (lazy (fsprintf "rassm_dec, prefix of judgment:@\n@[<hov 4>  %a@]"
                 pp_gdef prefix_ju));


  (* check that event equal to last returned value *)
  (match Util.last acalls_ju with
   | GLet(vs,_) ->
     if not (e_equal se.se_ev (mk_V vs)) then
       tacerror "assm_dec: event must be equal to variable defined in last line";
   | _ ->
     tacerror "assm_dec: event must be equal to variable defined in last line");

  (* check that we can instantiate adversary calls in assumption with remainder of ju *)
  let gdef_new_ju = ref prefix_new in
  let len_ju = L.length se.se_gdef in
  let priv_vars = private_vars_dec assm in
  let rec valid_ranges checked rngs acalls_ju acalls =
    match rngs, acalls with
    | (i,j)::rngs, (_,vres,(e1,e2))::acalls ->
      let e_old,e_new = swap_dir (e1,e2) in
      let len = j - i + 1 in
      let len_res = L.length vres in
      let len_body = len - 1 - len_res in
      if (i <> checked || len > L.length acalls_ju || len_body < 0) then
        tacerror "assm_dec: ranges do no cover games";
      let c_arg  = L.hd acalls_ju in
      let c_body = Util.take len_body (Util.drop 1 acalls_ju) in
      let c_res  = Util.take len_res (Util.drop (1 + len_body) acalls_ju) in

      (* check that return variables match and sampled variables are not used *)
      let read = read_gcmds (c_body@c_res) in
      if (not (Se.is_empty (Se.inter read priv_vars))) then
        tacerror "assm_dec: judgment uses private variables: %a in @\n%a@\narg: %a"
          (pp_list "," pp_exp) (Se.elements (Se.inter read priv_vars))
          pp_gdef (c_body@c_res)
          pp_gdef [c_arg];

      (* check that everything except adversary argument ppt *)
      if not (is_ppt_gcmds (c_body@c_res)) then (
        log_t (lazy (fsprintf "assm_dec: %a is not ppt" pp_gdef (c_body@c_res)));
        tacerror "assm_dec: %a is not ppt" pp_gdef (c_body@c_res)
      );
      
      (* check and replace argument for adversary call *)
      (match c_arg with
       | GLet (v_arg, e_arg) ->
         if (not (e_equal e_arg e_old)) then
           tacerror "assm_dec: arguments not equal:@\n %a vs %a"
             pp_exp e_arg pp_exp e_old;
         gdef_new_ju := !gdef_new_ju @ [GLet(v_arg,e_new)] @ c_body @ c_res
       | _ ->
         tacerror "assm_dec: range must start with let");
 
      (* continue with next range/adversary call *)
      valid_ranges (j+1) rngs (Util.drop len acalls_ju) acalls

    | [], [] ->
      if (checked <> len_ju) then tacerror "assm_dec: ranges do no cover games"

    | _, _ ->
      tacerror "assm_dec: ranges and adversary calls do not match up"
  in
  valid_ranges (L.length prefix_ju) rngs acalls_ju assm.ad_acalls;

  log_d (lazy (fsprintf "rassm_dec performed"));
  Rassm_dec(rngs,dir,ren,assm0), [{ ju with ju_se = { se with se_gdef = !gdef_new_ju }}]

let t_assm_dec dir ren rngs assm = prove_by (rassm_dec dir ren rngs assm)

(** Reduction to computational assumption. *)

let rassm_comp assm0 rngs ren ju =
  (*i FIXME: associate probability with assumption and check here i*)
  let se = ju.ju_se in
  if not (ren_injective ren)
    then tacerror "assm_comp: renaming is not bijective";
  let assm = Assumption.inst_comp ren assm0 in
  let prefix = assm.ac_prefix in
  let prefix_len = L.length prefix in
  let prefix_ju = Util.take prefix_len se.se_gdef in
  let acalls_ju = Util.drop prefix_len se.se_gdef in
  log_t (lazy (fsprintf "rassm_comp, renamed assumption:@\n@[<hov 4>  %a@]"
                 pp_assm_comp assm));
  log_t (lazy (fsprintf "rassm_comp, prefix of judgment:@\n@[<hov 4>  %a@]"
                 pp_gdef prefix_ju));

  (* check that prefix and event equal *)
  if not (gdef_equal prefix prefix_ju) then
    tacerror "assm_comp: prefixes not equal, @\n@[<hov 2>  %a@] vs @[<hov 2>  %a@]"
      pp_gdef prefix pp_gdef prefix_ju;
  if not (e_equal se.se_ev assm.ac_event) then
    tacerror "assm_comp: events not equal, @\n@[<hov 2>  %a vs @ %a@]"
      pp_exp se.se_ev pp_exp assm.ac_event;

  (* check that we can instantiate adversary calls in assumption with remainder of ju *)
  let len_ju = L.length se.se_gdef in
  let priv_vars = private_vars_comp assm in
  let rec valid_ranges checked rngs acalls_ju acalls =
    match rngs, acalls with
    | [], [] ->
      if (checked <> len_ju) then tacerror "assm_comp: ranges do no cover games"

    | _::_, [] |  [], _::_ ->
      tacerror "assm_comp: ranges and adversary calls do not match up"

    | (i,j)::rngs, (_,vres,e)::acalls ->
      let len = j - i + 1 in
      let len_res = L.length vres in
      let len_body = len - 1 - len_res in
      if (i <> checked || len > L.length acalls_ju || len_body < 0) then
        tacerror "assm_comp: ranges do no cover games";
      let c_arg  = L.hd acalls_ju in
      let c_body = Util.take len_body (Util.drop 1 acalls_ju) in
      let c_res  = Util.take len_res (Util.drop (1 + len_body) acalls_ju) in

      (* check that return variables match and sampled variables are not used *)
      let read = read_gcmds (c_body@c_res) in
      if (not (Se.is_empty (Se.inter read priv_vars))) then
        tacerror "assm_comp: judgment uses private variables: %a in @\n%a@\narg: %a"
          (pp_list "," pp_exp) (Se.elements (Se.inter read priv_vars))
          pp_gdef (c_body@c_res)
          pp_gdef [c_arg];

      (* check that everything except adversary argument ppt *)
      if not (is_ppt_gcmds (c_body@c_res)) then (
        log_t (lazy (fsprintf "assm_dec: %a is not ppt" pp_gdef (c_body@c_res)));
        tacerror "assm_dec: %a is not ppt" pp_gdef (c_body@c_res)
      );
      
      (* check and replace argument for adversary call *)
      (match c_arg with
       | GLet (_, e_arg) ->
         if (not (e_equal e_arg e)) then
           tacerror "assm_dec: arguments not equal:@\n %a vs %a"
             pp_exp e_arg pp_exp e;
       | _ ->
         tacerror "assm_dec: range must start with let");
 
      (* continue with next range/adversary call *)
      valid_ranges (j+1) rngs (Util.drop len acalls_ju) acalls

  in
  valid_ranges (L.length prefix_ju) rngs acalls_ju assm.ac_acalls;
  log_d (lazy (fsprintf "rassm_comp performed!"));
  Rassm_comp(rngs,ren,assm0), []

let t_assm_comp assm ev_e subst = prove_by (rassm_comp assm ev_e subst)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Terminal rules for finishing a proof} *)

(** Admit rule and tactic. *)

let radmit s _g = Radmit s, []
let t_admit s = prove_by (radmit s)

(** Bound false event by $0$. *)

let rfalse_ev ju =
  (*i FIXME: check ju_pr i*)
  let se = ju.ju_se in
  if is_False se.se_ev
  then (
    log_d (lazy (fsprintf "rfalse_ev"));
    Rfalse_ev, []
  ) else (
    tacerror "rfalse_ev: event false expected"
  )

let t_false_ev = prove_by rfalse_ev

(** Bound random independence. *)

let check_event r ev =
  let rec aux i evs =
    match evs with
    | [] ->
      tacerror "can not apply rindep for variable %a and event@\  %a@\n"
        Vsym.pp r pp_exp ev
    | ev::evs ->
      let r = mk_V r in
      let test_eq e1 e2 = e_equal e1 r && not (Se.mem r (e_vars e2)) in
      let check_eq e1 e2 =
        if test_eq e1 e2 then (
          log_d (lazy (fsprintf "rindep applied to %i" i));
          Rrnd_indep(true, i)
        ) else if test_eq e2 e1 then (
          log_d (lazy (fsprintf "rindep applied to %i" i));
          Rrnd_indep(false, i)
        )else raise Not_found in
      try
        if is_Eq ev then
          let e1, e2 = destr_Eq ev in
          check_eq e1 e2
        else if is_Exists ev then
          let e1,e2,_ = destr_Exists ev in
          check_eq e1 e2
        else aux (i+1) evs
      with Not_found -> aux (i+1) evs
  in
  aux 0 (destr_Land_nofail ev)

let rrandom_indep ju =
  let se = ju.ju_se in
  match L.rev se.se_gdef with
  | GSamp(r,_)::_ -> check_event r se.se_ev,  []
  | _             -> tacerror "rindep: the last instruction is not a random"

let t_random_indep = prove_by rrandom_indep
