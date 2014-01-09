(** Core rules of the logic. *)
open Util
open Type
open Expr
open Game
open Wf
open Assumption

(* final representation of a proof *)
type rule_name = 
  | Radmit 
  | Rconv
  | Rctxt_ev   of gcmd_pos * ctxt 
  | Rremove_ev of int list
  | Rmerge_ev  of int * int 
  | Rrandom    of gcmd_pos * ctxt * ctxt * Vsym.t
  | Rrnd_orcl  of ocmd_pos * ctxt * ctxt * Vsym.t
  | Rexcept    of gcmd_pos * expr list
  | Rexc_orcl  of ocmd_pos * expr list 
  | Radd_test  of ocmd_pos * expr * Asym.t * Vsym.t list 
  | Rrw_orcl   of ocmd_pos * direction
  | Rswap      of gcmd_pos * int 
  | Rswap_orcl of ocmd_pos * int 
  | Rrnd_indep of bool * int
  | Rassm_dec  of direction * Vsym.t Vsym.M.t * assumption_decision
  | Rbad       of gcmd_pos * Vsym.t 
type proof_tree = 
  { dr_subgoal : proof_tree list;
    dr_rule    : rule_name;
    dr_ju      : judgment; }


(* intermediate representation of a proof *)

type rule = judgment -> rule_name * judgment list
type validation = proof_tree list -> proof_tree

type goal = judgment

type goals = {
  subgoals   : judgment list;
  validation : validation
}

type tactic = goal -> goals 

type proof_state = goals 

exception Invalid_rule of string 
exception NoOpenGoal 

let tacerror fmt =
  let buf  = Buffer.create 127 in
  let fbuf = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush fbuf ();
      raise (Invalid_rule (Buffer.contents buf)))
    fbuf fmt

let fail_if_occur vs ju s =
  if (Se.mem (mk_V vs) (ju_vars ju)) then
    tacerror "%s: variable %a occurs in judgment\n %a"
      s Vsym.pp vs pp_ju ju 

let get_proof gs = 
  if gs.subgoals <> [] then tacerror "still subgoal";
  gs.validation []

let t_first_last gs = 
  match gs.subgoals with
  | [] -> tacerror "last: no goals"
  | ju :: jus ->
    let validation pts = 
      match List.rev pts with
      | pt :: pts -> gs.validation (pt::List.rev pts)
      | _ -> assert false in
    { subgoals = jus @ [ju];
      validation = validation }
        
let t_on_n n t gs = 
  let len = List.length gs.subgoals in
  if len = 0 then raise NoOpenGoal;
  if len <= n then tacerror "there is only %i subgoals" len;
  let hd, g, tl = 
    Util.split_n n gs.subgoals  
  in
  let gsn = t g in
  let vali pts =
    let hd, tl = Util.cut_n n pts in
    let ptn, tl = Util.cut_n (List.length gsn.subgoals) tl in
    gs.validation (List.rev_append hd (gsn.validation (List.rev ptn) :: tl))
  in
  { subgoals = List.rev_append hd (gsn.subgoals @ tl);
    validation = vali }

let t_last t gs = 
  t_on_n (List.length gs.subgoals - 1) t gs

let t_first t gs = 
  t_on_n 0 t gs

let merge_subgoals gs2s validation =
  let rec validation' accu gs2s pts = 
    match gs2s with
    | [] -> assert (pts = []); validation (List.rev accu)
    | gs2i::gs2s ->
      let hd, tl = Util.cut_n (List.length gs2i.subgoals) pts in
      validation' (gs2i.validation (List.rev hd) :: accu) gs2s tl in
  { subgoals   = List.flatten (List.map (fun gs -> gs.subgoals) gs2s);
    validation = validation' [] gs2s }

(** Composition tactics *)    

let t_id g = 
  { subgoals = [g];
    validation = fun pts -> match pts with [pt] -> pt | _ -> assert false }
    
let t_seq t1 t2 g = 
  let gs1 = t1 g in
  let gs2s = List.map t2 gs1.subgoals in
  merge_subgoals gs2s gs1.validation
 
let t_subgoal lt gs = 
  let gs2s = 
    try List.map2 (fun t g -> t g) lt gs.subgoals 
    with Invalid_argument _ -> 
      tacerror "%i tactics expected, %i are given" 
        (List.length gs.subgoals) (List.length lt)
  in
  merge_subgoals gs2s gs.validation

let t_try t g = 
  try t g with Invalid_rule _ -> t_id g

let t_or t1 t2 g = 
  try t1 g with Invalid_rule _ -> t2 g


(* ----------------------------------------------------------------------- *)
(** {2 Low level rules} *)
    
let prove_by g (rule, subgoals) = 
  { subgoals = subgoals;
    validation = fun pts -> 
      assert (List.length pts = List.length subgoals);
      assert (List.for_all2 (fun dr g -> ju_equal dr.dr_ju g) pts subgoals);
      {dr_ju      = g;
       dr_rule    = rule;
       dr_subgoal = pts; }}

let radmit _ju = Radmit, []
let t_admit ju = 
  prove_by ju (radmit ju)

(** Conversion *)
let rconv do_norm_terms new_ju ju =
  let (nf,ctype) =
    if do_norm_terms
    then (Norm.norm_expr,CheckDivZero)
    else (id,NoCheckDivZero)
  in
  wf_ju ctype ju;
  wf_ju ctype new_ju;
  let ju' = norm_ju ~norm:nf ju in
  let new_ju' = norm_ju ~norm:nf new_ju in
  if not (ju_equal ju' new_ju') then tacerror "rconv: not convertible";
  Rconv, [new_ju]

let t_conv do_norm_terms new_ju ju =
  prove_by ju (rconv do_norm_terms new_ju ju)

(** Transformation of the event *)
(* Applying context to ev *)
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

let t_ctxt_ev i c ju =
  prove_by ju (rctxt_ev i c ju)

(* Removing events *)
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
  (* TODO : should we check DivZero *)
  Rremove_ev rm, [new_ju]

let t_remove_ev rm ju = 
  prove_by ju (rremove_ev rm ju)

(* Merging events *)
let merge_base_event ev1 ev2 =
  match ev1.e_node, ev2.e_node with
  | App (Eq,[e11;e12]), App(Eq,[e21;e22]) ->
    mk_Eq (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22])
  | App (Eq,[e11;e12]), Exists(e21,e22, l) ->
    mk_Exists (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22]) l
  | Exists(e11,e12, l), App (Eq,[e21;e22]) ->
    mk_Exists (mk_Tuple [e11;e21]) (mk_Tuple [e12;e22]) l
  | Exists(e11,e12, l1), Exists(e21,e22, l2) ->  
  (* TODO we should be sure that bounded variables in l1 and l2 are disjoint *)
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
  (* TODO : should we check DivZero, I think not *)
  Rmerge_ev(i,j), [new_ju]

let t_merge_ev i j ju = 
  prove_by ju (rmerge_ev i j ju)

(** random rules *)

let ensure_bijection c1 c2 v =
  if not (Norm.e_equalmod (inst_ctxt c2 (inst_ctxt c1 v)) v &&
          Norm.e_equalmod (inst_ctxt c1 (inst_ctxt c2 v)) v)
  then tacerror "random: contexts not bijective"

(* 'random p c1 c2 vslet' takes a position p, two contexts. and a
   variable symbol for the new let-bound variable. It first
   ensures that there is a random sampling 'x <-$ d' at position p.
   For now, excepted distributions are not allowed.
   Then it checks that c1 and c2 are well-formed for at position p
   (taking inequalities that are checked beforehand into account)
   and that 'forall x in supp(d), c2(c1(x)) = x /\ c1(c2(x)) = x'.  *)
let rrandom p c1 c2 vslet ju =
  fail_if_occur vslet ju "rrandom";
  match get_ju_ctxt ju p with
  | GSamp(vs,((t,[]) as d)), juc ->
    assert (ty_equal vslet.Vsym.ty t);
    let v = mk_V vs in
    ensure_bijection c1 c2 v;
    let cmds = [ GSamp(vs,d);
                 GLet(vslet, inst_ctxt c1 (mk_V vs)) ]
    in
    let wfs = wf_gdef NoCheckDivZero (List.rev juc.juc_left) in
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c1)) (snd c1);
    wf_exp CheckDivZero (ensure_varname_fresh wfs (fst c2)) (snd c2);
    let subst e = e_replace v (mk_V vslet) e in
    let juc = { juc with
                juc_right = map_gdef_exp subst juc.juc_right;
                juc_ev = subst juc.juc_ev }
    in
    Rrandom(p,c1,c2,vslet), [ set_ju_ctxt cmds juc ]
  | _ -> tacerror "random: position given is not a sampling"

let t_random p c1 c2 vslet ju = 
  prove_by ju (rrandom p c1 c2 vslet ju)

(* random rule in oracle *)
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

let t_random_oracle  p c1 c2 vslet ju = 
 prove_by ju (rrandom_oracle p c1 c2 vslet ju)


(** Statistical distance *)

let rexcept p es ju =
  match get_ju_ctxt ju p with
  | GSamp(vs,(t,_es)), juc ->
    Rexcept(p, es), [ set_ju_ctxt [ GSamp(vs,(t,es)) ] juc ]
  | _ -> tacerror "rexcept: position given is not a sampling"

let t_except p es ju = 
  prove_by ju (rexcept p es ju)

let rexcept_oracle p es ju =
  match get_ju_octxt ju p with
  | LSamp(vs,(t,_es)), juoc ->
    Rexc_orcl(p,es), [ set_ju_octxt [ LSamp(vs,(t,es)) ] juoc ]
  | _ -> tacerror "rexcept_oracle: position given is not a sampling"

let t_except_oracle p es ju = 
  prove_by ju (rexcept_oracle p es ju)

(** Up-to bad: adding a new test to oracle *)

(* We get two new judgments for G : E after
   applying 'radd_test (i,j,k) t' vz A':
   G' : E (where the test t' is added to the oracle)
   and
   G'_{1..i}; vz <- A() : t /\ t'
   (where t is the test in the oracle *)
let radd_test p tnew asym fvs ju =
  match get_ju_octxt ju p with
  | LGuard(t), juoc ->
    assert (ty_equal tnew.e_ty mk_Bool);
    let destr_guard lcmd = match lcmd with
      | LGuard(e) -> e
      | _ ->
        tacerror ("radd_test: new test cannot be insert after %a, " ^^
                   "preceeding commands must be tests")
             pp_lcmd lcmd in
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
    Radd_test(p, tnew, asym, fvs), [ set_ju_octxt [ LGuard(t) ] juoc;
      set_ju_octxt [ LGuard(t) ]
        { juoc with
          juoc_juc =
            { juoc.juoc_juc with
              juc_ev = e_subst subst (mk_Land (tests@[ t ; mk_Not tnew]));
              juc_right = [ GCall(fvs,asym,mk_Tuple [],[]) ]
            }
        };
    ]
  | _ -> tacerror "rexcept_oracle: position given is not a sampling"

let t_add_test p tnew asym fvs ju = 
  prove_by ju (radd_test p tnew asym fvs ju)

(** Rewriting oracles using tests *)

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

let t_rewrite_oracle op dir ju = 
  prove_by ju (rrewrite_oracle op dir ju)
(** Swapping instructions *)

let disjoint s1 s2 = 
  Se.is_empty (Se.inter s1 s2)

let check_swap read write i c =
  let i = [i] in
  let ir = read i in
  let iw = write i in
  let cr = read c in
  let cw = write c in
  if not (disjoint iw cw && 
            disjoint ir cw &&
            disjoint cr iw) then 
    tacerror "swap : can not swap" (* FIXME improve the error message *)
    
let swap i delta ju = 
  if delta = 0 then ju
  else
    let i,{juc_left=hd; juc_right=tl; juc_ev=e} = get_ju_ctxt ju i in
    let c1,c2,c3 = 
      if delta < 0 then 
        let hhd, thd = cut_n (-delta) hd in
        thd, hhd, tl
      else
        let htl, ttl = cut_n delta tl in
        hd, List.rev htl, ttl in
    check_swap read_gcmds write_gcmds i c2;
    if is_call i && has_call c2 then
      tacerror "swap : can not swap";
    let c2,c3 = if delta > 0 then c2, i::c3 else i::c2, c3 in
    set_ju_ctxt c2 {juc_left=c1; juc_right=c3; juc_ev=e}

let rswap i delta ju = Rswap(i, delta), [swap i delta ju]

let t_swap i delta ju = 
  prove_by ju (rswap i delta ju)

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

let t_swap_oracle i delta ju =
  prove_by ju (rswap_oracle i delta ju)
 
(** Random indep *)

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
      with Not_found -> aux (i+1) evs in
  aux 0 (destruct_Land ev)



let rrandom_indep ju = 
  match List.rev ju.ju_gdef with
  | GSamp(r,_) :: _ ->
    check_event r ju.ju_ev,  []
  | _ -> tacerror "rrandom_indep: the last instruction is not a random"

let t_random_indep ju = 
  prove_by ju (rrandom_indep ju)
  
(** Reduction to decisional assumptions *)

let rassm_decision dir subst assm ju =
  let assm = Assumption.subst subst assm in
  let c,c' = 
    if dir = LeftToRight then assm.ad_prefix1,assm.ad_prefix2 
    else assm.ad_prefix2,assm.ad_prefix1 in
  let cju = Util.take (List.length c) ju.ju_gdef in
  if not (gdef_equal c cju) then 
    tacerror "Can not match the decisional assumption";
  let tl = Util.drop (List.length c) ju.ju_gdef in
  let ju' = { ju with ju_gdef = tl } in
  let read = read_ju ju' in
  let priv = Vsym.S.fold (fun x -> Se.add (mk_V x)) assm.ad_privvars Se.empty in
  let diff = Se.inter priv read in
  if not (Se.is_empty diff) then
    tacerror "Does not respect the private variables";
  if not (is_ppt_ju ju') then
    tacerror 
      "Does not respect the computational assumption (game and event ppt)";
  Rassm_dec(dir,subst,assm), [{ ju with ju_gdef = c' @ tl }]

let t_assm_decision dir subst assm ju = 
  prove_by ju (rassm_decision dir subst assm ju)

(** Rules for random oracles *)

(* Bad rule, random oracle *)
let rbad p vsx ju =
  fail_if_occur vsx ju "rbad";
  match get_ju_ctxt ju p with
  | GLet(vs,e'), ctxt when is_H e' ->
    let h,e = destr_H e' in
    (* TODO CHECK THAT h is only used here *)
    let i = [GSamp(vs,(e'.e_ty,[]))] in
    let ju1 = set_ju_ctxt i ctxt in
    let vx = mk_V vsx in
    let ev = mk_Exists e vx [vsx,h] in
    let ju2 = { ju1 with ju_ev = ev } in
    Rbad(p,vsx), [ju1;ju2]
  | _ -> 
    tacerror "can not apply bad rule"

let t_bad p vsx ju =
  prove_by ju (rbad p vsx ju)


