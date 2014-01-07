(** Core rules of the logic. *)
open Util
open Type
open Expr
open Game
open Wf
open Assumption

(* ----------------------------------------------------------------------- *)
(** {1 Rules and tactic language} *)

exception Invalid_rule of string

let fail_rule s = raise (Invalid_rule s)

(** goal handling *)

let apply rule goals = match goals with
  | g::gs ->
      let gs' = rule g in
      List.iter (wf_ju NoCheckDivZero) gs';
      gs' @ gs
  | _ -> fail_rule "there are no goals"

(* ----------------------------------------------------------------------- *)
(** {2 Low level rules} *)

(** Helper functions *)

let fail_if_occur vs ju s =
  if (Se.mem (mk_V vs) (ju_vars ju)) then
    fail_rule
      (fsprintf "%s: variable %a occurs in judgment\n %a"
         s Vsym.pp vs pp_ju ju |> fsget)

(** Conversion *)

(* let check_conv ju1 ju2 = 
  ju_equal (norm_ju ju1) (norm_ju ju2) 
*)

let rconv do_norm_terms new_ju1 ju1 =
  let (nf,ctype) =
    if do_norm_terms
    then (Norm.norm_expr,CheckDivZero)
    else (id,NoCheckDivZero)
  in
  wf_ju ctype ju1;
  wf_ju ctype new_ju1;
  let ju = norm_ju ~norm:nf ju1 in
  let new_ju = norm_ju ~norm:nf new_ju1 in
  if not (ju_equal ju new_ju) then
    (  
      Format.printf "ju = %a@.new_ju = %a@." 
        pp_ju ju pp_ju new_ju;
      let cc = List.combine ju.ju_gdef new_ju.ju_gdef in
      (try
         let (i1,i2) = List.find (fun (i1,i2) -> not (gcmd_equal i1 i2)) cc in
         Format.printf "i1 = %a@.i2 = %a@." pp_gcmd i1 pp_gcmd i2
       with _ -> Format.printf "????@.");
      flush_all (); 
      fail_rule "rconv: not convertible");
  [new_ju1]

(** Transformation of the event *)
(* Applying context to ev *)
let rctxt_ev (c : ctxt) (i : int) ju = 
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
    else fail_rule "rctxt_ev: bad event, expected equality or x in L"
  in
  let ev = mk_Land (List.rev_append l (b:: r)) in
  let wfs = wf_gdef NoCheckDivZero (ju.ju_gdef) in
  wf_exp CheckDivZero wfs ev;
  let new_ju = {ju with ju_ev = ev} in
  [new_ju]

(* Removing an event *)

let remove_ev (rm:int list) ju = 
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
  [new_ju]
  
(* Merging event *)

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

let merge_ev i j ju =
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
  [new_ju]

    

(** random rules *)

let ensure_bijection c1 c2 v =
  if not (Norm.e_equalmod (inst_ctxt c2 (inst_ctxt c1 v)) v &&
          Norm.e_equalmod (inst_ctxt c1 (inst_ctxt c2 v)) v)
  then fail_rule "random: contexts not bijective"

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
    [ set_ju_ctxt cmds juc ]
  | _ -> fail_rule "random: position given is not a sampling"

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
    [ set_ju_octxt cmds juoc ]
  | _ -> fail_rule "random: position given is not a sampling"

(** Statistical distance *)

let rexcept p es ju =
  match get_ju_ctxt ju p with
  | GSamp(vs,(t,_es)), juc ->
    [ set_ju_ctxt [ GSamp(vs,(t,es)) ] juc ]
  | _ -> fail_rule "rexcept: position given is not a sampling"

let rexcept_oracle p es  ju =
  match get_ju_octxt ju p with
  | LSamp(vs,(t,_es)), juoc ->
    [ set_ju_octxt [ LSamp(vs,(t,es)) ] juoc ]
  | _ -> fail_rule "rexcept_oracle: position given is not a sampling"

(** Up-to bad: adding a new test to oracle *)

(* We get tow new judgments for G : E after
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
        fail_rule
          (fsprintf ("radd_test: new test cannot be insert after %a, "
             ^^"preceeding commands must be tests")
             pp_lcmd lcmd |> fsget)
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
    [ set_ju_octxt [ LGuard(t) ] juoc;
      set_ju_octxt [ LGuard(t) ]
        { juoc with
          juoc_juc =
            { juoc.juoc_juc with
              juc_ev = e_subst subst (mk_Land (tests@[ t ; mk_Not tnew]));
              juc_right = [ GCall(fvs,asym,mk_Tuple [],[]) ]
            }
        };
    ]
  | _ -> fail_rule "rexcept_oracle: position given is not a sampling"


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
    [ set_ju_octxt [lc] juoc ]
  | _ -> assert false

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
    fail_rule "swap : can not swap" (* FIXME improve the error message *)
    
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
      fail_rule "swap : can not swap";
    let c2,c3 = if delta > 0 then c2, i::c3 else i::c2, c3 in
    set_ju_ctxt c2 {juc_left=c1; juc_right=c3; juc_ev=e}

let rswap i delta ju = [swap i delta ju]

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
  [swap_oracle i delta ju]
 
(** Random indep *)

let rec check_event r ev =
  if is_Nary Land ev then
    List.exists (check_event r) (destr_Land ev)
  else
    let r = mk_V r in
    if is_Eq ev then
      let e1, e2 = destr_Eq ev in
      let test_eq e1 e2 =
        e_equal e1 r && not (Se.mem r (e_vars e2))
      in test_eq e1 e2 || test_eq e2 e1
    else if is_Exists ev then
      let e1,e2,_ = destr_Exists ev in
      e_equal e1 r && not (Se.mem r (e_vars e2))
    else false

let rrandom_indep ju = 
  match List.rev ju.ju_gdef with
  | GSamp(r,_) :: _ when check_event r ju.ju_ev -> []
  | _ -> fail_rule "can not apply rrandom_indep"

(** Reduction to decisional assumptions *)

let rassm_decision dir subst assm ju =
  let assm = Assumption.subst subst assm in
  let c,c' = 
    if dir = LeftToRight then assm.ad_prefix1,assm.ad_prefix2 
    else assm.ad_prefix2,assm.ad_prefix1 in
  let cju = Util.take (List.length c) ju.ju_gdef in
  if not (gdef_equal c cju) then 
    fail_rule "Can not match the decisional assumption";
  let tl = Util.drop (List.length c) ju.ju_gdef in
  let ju' = { ju with ju_gdef = tl } in
  let read = read_ju ju' in
  let priv = Vsym.S.fold (fun x -> Se.add (mk_V x)) assm.ad_privvars Se.empty in
  let diff = Se.inter priv read in
  if not (Se.is_empty diff) then
    fail_rule "Does not respect the private variables";
  if not (is_ppt_ju ju') then
    fail_rule "Does not respect the computational assumption (game and event ppt)";
  [{ ju with ju_gdef = c' @ tl }]

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
    [ju1;ju2]
  | _ -> 
    fail_rule "can not apply bad rule"

