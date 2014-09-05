(*s Core rules of the logic. *)

(*i*)
open Util
open Type
open Expr
open Game
open Wf
open Assumption
open Syms
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Types for proofs and tactics} *)

(** Renaming of variables. *)
type renaming = vs Vsym.M.t

let id_renaming = Vsym.M.empty

(** Low-level rules (extractable to EasyCrypt). *)
type rule_name = 

  (*c equivalence/small statistical distance: main *)
  | Rconv                                  (*r rename, unfold let, normalize *)
  | Rswap   of gcmd_pos * int              (*r
      $Rswap(p,i)$: swap statement at $p$ forward by $i$ *)
  | Rrnd    of gcmd_pos * ctxt * ctxt (*r
      $Rnd(p,c_1,c_2,v)$: rnd with bij. $c_1=c_2^{-1}$ for $v$ at $p$*)
  | Rexc of gcmd_pos * expr list (*r
      $Rexc(p,\vec{e})$: change sampling at $p$ to exclude $\vec{e}$ *)

  (*c equivalence/small statistical distance: oracle *)
  | Rrw_orcl   of ocmd_pos * direction (*r
      $Rrw\_orcl(p,dir)$: rewrite oracle with equality test at $p$ in $dir$ *)
  | Rswap_orcl of ocmd_pos * int (*r
      $Rswap\_orcl(op,i)$: swap statement at $p$ forward by $i$ *)
  | Rrnd_orcl  of ocmd_pos * ctxt * ctxt * vs (*r
      $Rnd\_orcl(p,c_1,c_2,v)$: rnd with $c_1=c_2^{-1}$ for $v$ at $p$*)
  | Rexc_orcl  of ocmd_pos * expr list (*r
      $Rexc\_orcl(p,\vec{e})$: change sampling at $p$ to exclude $\vec{e}$ *)

  (*c case distinctions, up-to *)
  | Rcase_ev  of expr (*r
      $Rcase(e)$: refine event by performing case distinction on $e$ *)
  | Radd_test of ocmd_pos * expr * ads * vs list (*r
      $Radd\_test(p,e,a,\vec{v})$: add test to oracle. *)
      (*c Test $e$ at position $p$, adversary $a$ and $\vec{v}$ used for bounding bad. *)
  | Rbad      of gcmd_pos * vs (*r
      $Rbad(p,v)$: Replace hash call at position $p$ by random variable $v$. *)

  (*c implication rules for event *)
  | Rctxt_ev   of int * ctxt (*r
      $Rctxt\_ev(i,c)$: apply context $c$ to $i$ conjunct in event *)
  | Rremove_ev of int list (*r $Rremove_ev(\vec{i})$: Remove given conjuncts *)
  | Rmerge_ev  of int * int (*r
      $Rmerge\_ev(i,j)$: Merge given conjuncts as equality on tuples. *)
  | Rsplit_ev  of int (*r
      $Rsplit\_ev(i)$: Split $i$-th event into separate equalities. *)
  | Rrw_ev     of int * direction (*r
      $Rrw\_ev(i,d)$: Rewrite event using $i$-th conjunct in direction $d$. *)

  (*c apply assumption *)
  | Rassm_dec  of direction * renaming  * assm_dec
  | Rassm_comp of expr * renaming * assm_comp

  (*c terminal rules *)
  | Radmit
  | Rfalse_ev
  | Rrnd_indep of bool * int

(** Proof tree. *)
type proof_tree = {
  pt_subgoal : proof_tree list;
  pt_rule    : rule_name;
  pt_ju      : judgment
}

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
type tactic = goal -> proof_state

(*i ----------------------------------------------------------------------- i*)
(* \subsection{General purpose functions} *)

(** Raised if there is no open goal. *)
exception NoOpenGoal 

(** Fail with message [s] if variable [vs] occurs in [ju]. *)
let fail_if_occur vs ju s =
  if (Vsym.S.mem vs (gdef_all_vars ju.ju_gdef)) then
    tacerror "%s: variable %a occurs in judgment\n %a" s Vsym.pp vs pp_ju ju

(** Prove goal [g] by rule [ru] which yields [subgoals]. *)
let prove_by rule g = 
  let (rn, subgoals) = rule g in
  { subgoals = subgoals;
    validation = fun pts ->
      assert (List.length pts = List.length subgoals);
      assert (List.for_all2 (fun pt g -> ju_equal pt.pt_ju g) pts subgoals);
      { pt_ju      = g;
        pt_rule    = rn;
        pt_subgoal = pts;
      }
  }

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
(* \subsection{Tacticals and goal management} *)

(** Tactic that moves the first subgoal to the last position. *)
let t_first_last ps = 
  match ps.subgoals with
  | [] -> tacerror "last: no goals"
  | ju :: jus ->
    let validation pts = 
      match List.rev pts with
      | pt :: pts -> ps.validation (pt::List.rev pts)
      | _ -> assert false in
    { subgoals = jus @ [ju];
      validation = validation }

(** Apply the tactic [t] to the [n]-th subgoal of proof state [ps]. *)
let t_on_n n t ps = 
  let len = List.length ps.subgoals in
  if len = 0 then raise NoOpenGoal;
  if len <= n then tacerror "there is only %i subgoals" len;
  let hd, g, tl = 
    Util.split_n n ps.subgoals  
  in
  let gsn = t g in
  let vali pts =
    let hd, tl = Util.cut_n n pts in
    let ptn, tl = Util.cut_n (List.length gsn.subgoals) tl in
    ps.validation (List.rev_append hd (gsn.validation (List.rev ptn) :: tl))
  in
  { subgoals = List.rev_append hd (gsn.subgoals @ tl);
    validation = vali }

(** Apply the tactic [t] to the first subgoal in proof state [ps]. *)
let t_first t ps = t_on_n 0 t ps

(** Identity tactic. *)
let t_id g = 
  { subgoals = [g];
    validation = fun pts -> match pts with [pt] -> pt | _ -> assert false }

(** Apply [t1] to goal [g] and [t2] to all resulting subgoals. *)
let t_seq t1 t2 g =
  let ps1 = t1 g in
  let ps2s = List.map t2 ps1.subgoals in
  merge_proof_states ps2s ps1.validation

(** Apply tactics [ts] to subgoals of proof state [ps]. *)
let t_subgoal ts ps = 
  let ps2s = 
    try List.map2 (fun t g -> t g) ts ps.subgoals 
    with Invalid_argument _ -> 
      tacerror "%i tactics expected, %i are given" 
        (List.length ps.subgoals) (List.length ts)
  in
  merge_proof_states ps2s ps.validation

(** Apply tactic [t1] to goal [g] or [t2] in case of failure. *)
let t_or t1 t2 g = 
  try t1 g with Invalid_rule _ -> t2 g

(** Apply tactic [t] or [t_id] in case of failure. *)
let t_try t g = t_or t t_id g

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Rules for main (equivalence/small statistical distance)} *)

(** Conversion. *)

(** [rconv do_norm sigma new_ju ju] takes a boolean that
    determines if both judgments have to be normalized,
    then it checks that [sigma] is bijective and renames
    [ju] with [sigma] before
    normalizing and comparing the two judgments *)
let rconv do_norm_terms new_ju ju =
  let (nf,ctype) =
    if do_norm_terms
    then (Norm.norm_expr,CheckDivZero)
    else (id,NoCheckDivZero)
  in
  wf_ju ctype ju;
  wf_ju ctype new_ju;
  (* eprintf "ju >> %a\n%!" pp_ju ju; *)
  (* eprintf "new_ju >> %a\n%!" pp_ju new_ju; *)
  (* eprintf "sigma(ju) >> %a\n%!" pp_ju ju; *)
  let ju' = norm_ju ~norm:nf ju in
  let new_ju' = norm_ju ~norm:nf new_ju in
  let ju' =
    try
      let sigma = Game.unif_ju ju' new_ju' in
      if not (Game.subst_injective sigma) then
        tacerror "rconv: computed renaming is not bijective";
      subst_v_ju (fun vs -> Vsym.M.find vs sigma) ju'
    with
      Not_found -> ju'
  in
  if not (ju_equal ju' new_ju') then tacerror "rconv: not convertible";
  Rconv, [new_ju]

let t_conv do_norm_terms new_ju = prove_by (rconv do_norm_terms new_ju)

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
    let instr,{juc_left=hd; juc_right=tl; juc_ev=e} = get_ju_ctxt ju i in
    let c1,c2,c3 = 
      if delta < 0 then 
        let hhd, thd = cut_n (-delta) hd in
        thd, hhd, tl
      else
        let htl, ttl = cut_n delta tl in
        hd, List.rev htl, ttl
    in
    check_swap read_gcmds write_gcmds instr c2;
    if is_call instr && has_call c2
    then tacerror "swap : can not swap";
    let c2,c3 = if delta > 0 then c2, instr::c3 else instr::c2, c3 in
    set_ju_ctxt c2 {juc_left=c1; juc_right=c3; juc_ev=e}

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
let rrandom p c1 c2 ju =
  match get_ju_ctxt ju p with
  | GSamp(vs,((_t,[]) as d)), juc ->
    let v = mk_V vs in
    ensure_bijection c1 c2 v;
    let cmds =
      [ GSamp(vs,d);
        GLet(vs, inst_ctxt c1 (mk_V vs)) ]
    in
    let wfs = wf_gdef NoCheckDivZero (List.rev juc.juc_left) in
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c1)) (snd c1);
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c2)) (snd c2);
    let juc =
      { juc with
        juc_right = juc.juc_right;
        juc_ev = juc.juc_ev }
    in
    Rrnd(p,c1,c2), [ set_ju_ctxt cmds juc ]
  | _ -> tacerror "random: position given is not a sampling"

let t_random p c1 c2 = prove_by (rrandom p c1 c2)

(** Exclude from sampling. *)

let rexcept p es ju =
  match get_ju_ctxt ju p with
  | GSamp(vs,(t,_es)), juc ->
    Rexc(p, es), [ set_ju_ctxt [ GSamp(vs,(t,es)) ] juc ]
  | _ ->
    tacerror "rexcept: position given is not a sampling"

let t_except p es = prove_by (rexcept p es)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Rules for oracle (equivalence/small statistical distance)} *)

(** Rewrite oracle using test. *)

let rrewrite_oracle op dir ju =
  match get_ju_octxt ju op with
  | LGuard(t) as lc, juoc ->
    (* replace a by b *)
    let (a,b) = match t.e_node with
      | App(Eq,[u;v]) ->
        if dir = LeftToRight then (u,v) else (v,u)
      | _ -> assert false
    in
    let subst e = e_replace a b e in
    let juoc = { juoc with
                 juoc_cright = List.map (map_lcmd_exp subst) juoc.juoc_cright;
                 juoc_return = subst juoc.juoc_return }
    in
    Rrw_orcl(op,dir), [ set_ju_octxt [lc] juoc ]
  | _ -> assert false

let t_rewrite_oracle op dir = prove_by (rrewrite_oracle op dir)

(** Swap instruction. *)

let swap_oracle i delta ju = 
  if delta = 0 then ju
  else
    let i, juoc = get_ju_octxt ju i in
    let c1_rev,c2,c3 = 
      if delta < 0 then
        let hhd,thd = cut_n (-delta) juoc.juoc_cleft in
        thd,hhd,juoc.juoc_cright
      else
        let htl, ttl = cut_n delta juoc.juoc_cright in
        juoc.juoc_cleft, List.rev htl, ttl in
    check_swap read_lcmds write_lcmds i c2;
    let c2, c3 = 
      if delta > 0 then c2, i::c3 else i::c2, c3 in
    set_ju_octxt c2 { juoc with juoc_cleft = c1_rev; juoc_cright = c3 }

let rswap_oracle i delta ju =
  Rswap_orcl(i,delta), [swap_oracle i delta ju]

let t_swap_oracle i delta = prove_by (rswap_oracle i delta)

(** Random rule. *)

let rrandom_oracle p c1 c2 vslet ju =
  fail_if_occur vslet ju "rrandom_oracle";
  match get_ju_octxt ju p with
  | LSamp(vs,((t,[]) as d)), juoc ->
    assert (ty_equal vslet.Vsym.ty t);
    let v = mk_V vs in
    ensure_bijection c1 c2 v;
    let cmds = [ LSamp(vs,d);
                 LLet(vslet, inst_ctxt c1 (mk_V vs)) ]
    in
    (* ensure both contexts well-defined *)
    let wfs = wf_gdef CheckDivZero (List.rev juoc.juoc_juc.juc_left) in
    let wfs = ensure_varnames_fresh wfs juoc.juoc_oargs in
    let wfs = wf_lcmds CheckDivZero wfs (List.rev juoc.juoc_cleft) in
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c1)) (snd c1);
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c2)) (snd c2);
    let subst e = e_replace v (mk_V vslet) e in
    let juoc = { juoc with
                 juoc_return = subst juoc.juoc_return;
                 juoc_cright = List.map (map_lcmd_exp subst) juoc.juoc_cright }
    in
    Rrnd_orcl(p,c1,c2,vslet), [set_ju_octxt cmds juoc]
  | _ -> tacerror "random: position given is not a sampling"

let t_random_oracle p c1 c2 vslet = prove_by (rrandom_oracle p c1 c2 vslet)

(** Exclude values from sampling. *)

let rexcept_oracle p es ju =
  match get_ju_octxt ju p with
  | LSamp(vs,(t,_es)), juoc ->
    Rexc_orcl(p,es), [ set_ju_octxt [ LSamp(vs,(t,es)) ] juoc ]
  | _ -> tacerror "rexcept_oracle: position given is not a sampling"

let t_except_oracle p es = prove_by (rexcept_oracle p es)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Rules for case distinctions and up-to} *)

(** Perform case distinction on event. *)

let rcase_ev e ju =
  let ev = ju.ju_ev in
  let ju1 = {ju with ju_ev = mk_Land [ev;e] } in
  let ju2 = {ju with ju_ev = mk_Land [ev; (mk_Not e)] } in
  Rcase_ev(e), [ju1; ju2]

let t_case_ev e = prove_by (rcase_ev e)

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
let radd_test p tnew asym fvs ju =
  match get_ju_octxt ju p with
  | LGuard(t), juoc ->
    assert (ty_equal tnew.e_ty mk_Bool);
    let destr_guard lcmd =
      match lcmd with
      | LGuard(e) -> e
      | _ ->
        tacerror ("radd_test: new test cannot be inserted after %a, " ^^
                   "preceeding commands must be tests")
             pp_lcmd lcmd
    in
    let tests = List.map destr_guard (List.rev juoc.juoc_cleft) in
    let subst = 
      List.fold_left2
        (fun s ov fv -> Me.add (mk_V ov) (mk_V fv) s)
        Me.empty juoc.juoc_oargs fvs
    in
    let juoc =
      { juoc with (* we add the new test first *)
        juoc_cleft = juoc.juoc_cleft @ [ LGuard(tnew)] }
    in
    Radd_test(p, tnew, asym, fvs),
      [ set_ju_octxt [ LGuard(t) ]
          { juoc with
            juoc_juc =
              { juoc.juoc_juc with
                juc_ev = e_subst subst (mk_Land (tests@[ t ; mk_Not tnew]));
                juc_right = [ GCall(fvs,asym,mk_Tuple [],[]) ]
              }
          };
        set_ju_octxt [ LGuard(t) ] juoc
      ]
  | _ -> tacerror "radd_test: given position is not a test"

let t_add_test p tnew asym fvs = prove_by (radd_test p tnew asym fvs)

(** Bad rule for random oracle. *)

let rbad p vsx ju =
  fail_if_occur vsx ju "rbad";
  match get_ju_ctxt ju p with
  | GLet(vs,e'), ctxt when is_H e' ->
    let h,e = destr_H e' in
    if not (Hsym.is_ro h) then 
      tacerror "the function %a is not a random oracle" Hsym.pp h;
    (*i TODO CHECK THAT h is only used here, and that call are guarded in
       oracle i*)
    let i = [GSamp(vs,(e'.e_ty,[]))] in
    let ju1 = set_ju_ctxt i ctxt in
    let vx = mk_V vsx in
    let ev = mk_Exists e vx [vsx,h] in
    let ju2 = { ju1 with ju_ev = ev } in
    Rbad(p,vsx), [ju1;ju2]
  | _ -> 
    tacerror "can not apply bad rule"

let t_bad p vsx = prove_by (rbad p vsx)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Rules for implications between events} *)

(** Apply context to event. *)

let rctxt_ev i c ju =
  let ev = ju.ju_ev in
  let evs = destruct_Land ev in
  if i < 0 || i >= List.length evs then failwith "invalid event position";
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
  let ev = mk_Land (List.rev_append l (b:: r)) in
  let wfs = wf_gdef NoCheckDivZero (ju.ju_gdef) in
  wf_exp CheckDivZero wfs ev;
  let new_ju = {ju with ju_ev = ev} in
  Rctxt_ev(i, c), [new_ju]

let t_ctxt_ev i c = prove_by (rctxt_ev i c)

(** Remove events. *)

let rremove_ev (rm:int list) ju = 
  let rec aux i evs = 
    match evs with
    | [] -> []
    | ev::evs -> 
      let evs = aux (i+1) evs in
      if List.mem i rm then evs else ev::evs in
  let ev = ju.ju_ev in
  let evs = aux 0 (destruct_Land ev) in
  let new_ju = {ju with ju_ev = mk_Land evs} in
  (*i TODO : should we check DivZero i*)
  Rremove_ev rm, [new_ju]

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
    (*i TODO we should be sure that bound variables in l1 and l2 are disjoint i*)
    mk_Exists (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22]) (l1 @ l2)
  | _, _ -> failwith "do not knwon how to merge the event"

let rmerge_ev i j ju =
  let i,j = if i <= j then i, j else j, i in
  let evs = destruct_Land ju.ju_ev in
  let l,b1,r = Util.split_n i evs in 
  let l',b2,r = 
    if i = j then [], b1, r 
    else Util.split_n (j - i - 1) r in
  let ev = merge_base_event b1 b2 in
  let evs = List.rev_append l (List.rev_append l' (ev::r)) in
  let new_ju = {ju with ju_ev = mk_Land evs} in
  (*i TODO : should we check DivZero, I think not i*)
  Rmerge_ev(i,j), [new_ju]

let t_merge_ev i j = prove_by (rmerge_ev i j)

(** Split equality on products into multiple equalities. *)

let rsplit_ev i ju =
  let ev = ju.ju_ev in
  let evs = destruct_Land ev in
  if i < 0 || i >= List.length evs then failwith "invalid event position";
  let l,b,r = Util.split_n i evs in 
  let b =
    if not (is_Eq b)
      then tacerror "rsplit_ev: bad event, expected equality";
    let (e1,e2) = destr_Eq b in
    if not (is_Tuple e1 && is_Tuple e2)
      then tacerror "rsplit_ev: bad event, tuples";
    let es1, es2 = destr_Tuple e1, destr_Tuple e2 in
    if not (List.length es1 = List.length es2)
      then tacerror "rsplit_ev: bad event, tuples";
    List.map (fun (e1,e2) -> mk_Eq e1 e2) (List.combine es1 es2)
  in
  let evs = l@b@r in
  let new_ju = {ju with ju_ev = mk_Land evs} in
  Rsplit_ev(i), [ new_ju ]

let t_split_ev i = prove_by (rsplit_ev i)

(** Rewrite event with equality. *)

let rrw_ev i d ju =
  let ev = ju.ju_ev in
  let evs = destruct_Land ev in
  if i < 0 || i >= List.length evs then failwith "invalid event position";
  let l,b,r = Util.split_n i evs in 
  let u,v =
    if not (is_Eq b)
      then tacerror "rrw_ev: bad event, expected equality";
    let u,v = destr_Eq b in
    if d = LeftToRight then (u,v) else (v,u)
  in
  let subst e = e_replace u v e in
  let evs = (List.map subst l)@[b]@(List.map subst r) in
  let new_ju = { ju with ju_ev = mk_Land evs } in
  Rrw_ev(i,d), [ new_ju ]

let t_rw_ev i d = prove_by (rrw_ev i d)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Rules for decisional and computational assumptions} *)

(** Reduction to decisional assumptions. *)

let rassm_dec dir subst assm' ju =
  let assm = Assumption.subst subst assm' in
  let c,c' = 
    if dir = LeftToRight
    then assm.ad_prefix1,assm.ad_prefix2 
    else assm.ad_prefix2,assm.ad_prefix1
  in
  let cju = Util.take (List.length c) ju.ju_gdef in
  if not (gdef_equal c cju) then tacerror "assm_dec: cannot match decisional assumption";
  let tl = Util.drop (List.length c) ju.ju_gdef in
  let ju' = { ju with ju_gdef = tl } in
  let read = read_ju ju' in
  let priv = Vsym.S.fold (fun x -> Se.add (mk_V x)) assm.ad_privvars Se.empty in
  let diff = Se.inter priv read in
  if not (Se.is_empty diff) then tacerror "assm_dec: does not respect private variables";
  if not (is_ppt_ju ju') then tacerror "assm_dec: game or event not ppt";
  Rassm_dec(dir,subst,assm'), [{ ju with ju_gdef = c' @ tl }]

let t_assm_dec dir subst assm = prove_by (rassm_dec dir subst assm)

(** Reduction to computational assumption. *)

let rassm_comp assm ev_e subst ju =
  let assm = Assumption.instantiate subst assm in
  let assm_ev = e_replace (mk_V assm.ac_event_var) ev_e assm.ac_event in
  if ju.ju_ev <> assm_ev
  then (tacerror "assm_comp: event not equal, expected %a, got %a"
          pp_exp ju.ju_ev pp_exp assm_ev);
  let c = assm.ac_prefix in
  let cju = Util.take (List.length c) ju.ju_gdef in
  if not (gdef_equal c cju) then tacerror "assm_comp: prefix does not match";
  let tl = Util.drop (List.length c) ju.ju_gdef in
  let ju' = { ju with ju_gdef = tl } in
  let read = read_ju ju' in
  let priv = Vsym.S.fold (fun x -> Se.add (mk_V x)) assm.ac_privvars Se.empty in
  let diff = Se.inter priv read in
  if not (Se.is_empty diff) then tacerror "assm_comp: does not respect private variables";
  if not (is_ppt_ju ju') then tacerror "assm_comp: game or event not ppt";
  Rassm_comp(ev_e,subst,assm), []

let t_assm_comp assm ev_e subst = prove_by (rassm_comp assm ev_e subst)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Terminal rules for finishing a proof} *)

(** Admit rule and tactic. *)

let radmit _g = Radmit, []
let t_admit = prove_by radmit

(** Bound false event by $0$. *)

let rfalse_ev ju =
  if is_False ju.ju_ev
  then Rfalse_ev, []
  else tacerror "rfalse_ev: event false expected"

let t_false_ev = prove_by rfalse_ev
 
(** Bound random independence. *)

let check_event r ev =
  let rec aux i evs = 
    match evs with
    | [] -> tacerror "can not apply rrandom_indep"
    | ev::evs -> 
      let r = mk_V r in
      let test_eq e1 e2 = e_equal e1 r && not (Se.mem r (e_vars e2)) in
      let check_eq e1 e2 = 
        if test_eq e1 e2 then Rrnd_indep(true, i)
        else if test_eq e2 e1 then Rrnd_indep(false, i)
        else raise Not_found in
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
  aux 0 (destruct_Land ev)

let rrandom_indep ju = 
  match List.rev ju.ju_gdef with
  | GSamp(r,_)::_ -> check_event r ju.ju_ev,  []
  | _             -> tacerror "rrandom_indep: the last instruction is not a random"

let t_random_indep = prove_by rrandom_indep
