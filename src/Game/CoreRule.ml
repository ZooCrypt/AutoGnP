open Util
open Type
open Expr
open Game
open Wf

(* ----------------------------------------------------------------------- *)
(** {1 Rules and tactic language} *)

(** goal handling *)

let apply rule goals = match goals with
  | g::gs ->
      let gs' = rule g in
      List.iter wf_ju gs';
      gs' @ gs
  | _ -> failwith "there are no goals"

let delay goals = match goals with
  | g::gs -> gs@[g]
  | []    -> []

(* ----------------------------------------------------------------------- *)
(** {2 Low level rule} *)

let assert_no_occur vs ju s =
  assert_msg (not (Se.mem (mk_V vs) (ju_vars ju)))
    (fsprintf "%s: variable %a occurs in judgment\n %a"
        s Vsym.pp vs pp_ju ju |> fsget)

(** Conversion *)

let check_conv ju1 ju2 = 
  ju_equal (norm_ju ju1) (norm_ju ju2) 

let rconv new_ju1 ju1 = 

(*  Format.printf "%a@." pp_gdef (snd (Util.cut_n 6 new_ju1.ju_gdef)); *)
(*  Format.printf "%a@." pp_gdef (snd (Util.cut_n 6 ju1.ju_gdef)); *)
(*  Format.printf "Check conv@.ju = %a@." pp_ju ju1; 
  Format.printf "new_ju = %a@." pp_ju new_ju1; *)
  let ju = norm_ju ju1 in
  let new_ju = norm_ju new_ju1 in
(*  Format.printf "Check conv@.ju = %a@." pp_ju ju1; 
  Format.printf "new_ju = %a@." pp_ju new_ju1; 
  Format.printf "norm ju = %a@." pp_ju ju;
  Format.printf "norm new_ju = %a@." pp_ju new_ju; *)
  if not (ju_equal ju new_ju) then
    (  
      Format.printf "ju = %a@.new_ju = %a@." 
        pp_ju ju pp_ju new_ju;
      let cc = List.combine ju.ju_gdef new_ju.ju_gdef in
      (try
         let (i1,i2) = List.find (fun (i1,i2) -> not (gc_equal i1 i2)) cc in
         Format.printf "i1 = %a@.i2 = %a@." pp_gcmd i1 pp_gcmd i2
       with _ -> Format.printf "????@.");
      flush_all (); 
      failwith "rconv: not convertible");
  [new_ju1]

(** Applying context on ev *)
let rctxt_ev ev c ju = 
  let new_ju = {ju with ju_ev = ev} in
  let ev1 = ju.ju_ev in
  let cev1 = 
    if is_Eq ev1 then
      let (e1,e2) = destr_Eq ev1 in
      mk_Eq (inst_ctxt c e1) (inst_ctxt c e2) 
    else if is_ElemH ev1 then
      let (e1,e2,h) = destr_ElemH ev in
      mk_ElemH (inst_ctxt c e1) (inst_ctxt c e2) h 
    else failwith "rctxt_ev: bad event"
  in
  let ju' = {ju with ju_ev = cev1} in
  if not (check_conv new_ju ju') then 
    failwith "rctxt_ev: bad context";
  [new_ju]

(** random rule *)

let ensure_bijection c1 c2 v =
  if not (Norm.e_equalmod (inst_ctxt c2 (inst_ctxt c1 v)) v &&
          Norm.e_equalmod (inst_ctxt c1 (inst_ctxt c2 v)) v)
  then failwith "random: contexts not bijective"

(* 'random p c1 c2' takes a position p and two contexts. It first
   ensures that there is a random sampling 'x <-$ d' at position p.
   For now, its not excepted. Otherwise we have to apply c1/c2 to
   the excepted values.
   Then it checks that under the inequalities that hold at position p,
   forall x in supp(d), c2(c1(x)) = x /\ c1(c2(x)) = x.  *)
let rrandom p c1 c2 vslet ju =
  assert_no_occur vslet ju "rrandom";
  match get_ju_ctxt ju p with
  | GSamp(vs,((t,[]) as d)), juc ->
    assert (ty_equal vslet.Vsym.ty t);
    let v = mk_V vs in
    ensure_bijection c1 c2 v;
    let cmds = [ GSamp(vs,d);
                 GLet(vslet, inst_ctxt c1 (mk_V vs)) ]
    in
    let wfs = wf_gdef (List.rev juc.juc_left) in
    wf_exp (ensure_varname_fresh wfs (fst c1)) (snd c1);
    wf_exp (ensure_varname_fresh wfs (fst c2)) (snd c2);
    let subst e = e_replace v (mk_V vslet) e in
    let juc = { juc with
                juc_right = map_gdef_exp subst juc.juc_right;
                juc_ev = subst juc.juc_ev }
    in
    [ set_ju_ctxt cmds juc ]
  | _ -> failwith "random: position given is not a sampling"

(* random in oracle *)
let rrandom_oracle p c1 c2 vslet ju =
  assert_no_occur vslet ju "rrandom_oracle";
  match get_ju_octxt ju p with
  | LSamp(vs,((t,[]) as d)), juoc ->
    assert (ty_equal vslet.Vsym.ty t);
    let v = mk_V vs in
    ensure_bijection c1 c2 v;
    let cmds = [ LSamp(vs,d);
                 LLet(vslet, inst_ctxt c1 (mk_V vs)) ]
    in
    (* ensure both contexts well-defined *)
    let wfs = wf_gdef (List.rev juoc.juoc_juc.juc_left) in
    let wfs = ensure_varnames_fresh wfs juoc.juoc_oargs in
    let wfs = wf_lcmds wfs (List.rev juoc.juoc_cleft) in
    wf_exp (ensure_varname_fresh wfs (fst c1)) (snd c1);
    wf_exp (ensure_varname_fresh wfs (fst c2)) (snd c2);

    let subst e = e_replace v (mk_V vslet) e in
    let juoc = { juoc with
                 juoc_return = subst juoc.juoc_return;
                 juoc_cright = List.map (map_lcmd_exp subst) juoc.juoc_cright }
    in
    [ set_ju_octxt cmds juoc ]
  | _ -> failwith "random: position given is not a sampling"


(** Swapping instruction *)

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
    failwith "swap : can not swap" (* FIXME improve the error message *)
    
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
      failwith "swap : can not swap";
    let c2,c3 = if delta > 0 then c2, i::c3 else i::c2, c3 in
    set_ju_ctxt c2 {juc_left=c1; juc_right=c3; juc_ev=e}

let rswap i delta ju = [swap i delta ju]

let swap_oracle i delta ju = 
  if delta = 0 then ju
  else
    let i, juoc = get_ju_octxt ju i in
    let c1,c2,c3 = 
      if delta < 0 then
        let hhd,thd = cut_n delta juoc.juoc_cleft in
        thd,hhd,juoc.juoc_cleft
      else 
        let htl, ttl = cut_n delta juoc.juoc_cright in
        juoc.juoc_cright, List.rev htl, ttl in
    check_swap read_lcmds write_lcmds i c2;
    let c2, c3 = 
      if delta > 0 then c2, i::c3 else i::c2, c3 in
    set_ju_octxt c2 { juoc with juoc_cleft = c1; juoc_cright = c3 }

let rswap_oracle i delta ju =
  [swap_oracle i delta ju]
 
(** Random indep *)

let check_event r ev = 
  let r = mk_V r in
  if is_Eq ev then
    let e1, e2 = destr_Eq ev in
    e_equal e1 r && not (Se.mem r (e_vars e2))
  else if is_ElemH ev then
    let e1,e2,_ = destr_ElemH ev in
    e_equal e1 r && not (Se.mem r (e_vars e2))
  else false

let rrandom_indep ju = 
  match List.rev ju.ju_gdef with
  | GSamp(r,_) :: _ when check_event r ju.ju_ev -> []
  | _ -> failwith "can not apply rrandom_indep"
    

(** DDH hypothesis *)

let check_ddh a b ex ey ez c ev =
 let a = mk_V a in
 let b = mk_V b in
 let r = Se.union (read_gcmds c) (e_vars ev) in
 ty_equal a.e_ty mk_Fq &&
   ty_equal b.e_ty mk_Fq &&
   e_equal ex (mk_GExp mk_GGen a) &&
   e_equal ey (mk_GExp mk_GGen b) &&
   e_equal ez (mk_GExp mk_GGen (mk_FMult [a;b])) &&
   not (Se.mem a r) && not (Se.mem b r) &&
   not (has_log_gcmds c) && not (has_log ev) 

let rddh vsc ju =
  assert_no_occur vsc ju "rddh";
  let vc = mk_V vsc in
  match ju.ju_gdef with
  | (GSamp(a,(_ta,[])) as i1) ::
    (GSamp(b,(_tb,[])) as i2) ::
    (GLet (_x,ex) as i3) ::
    (GLet (_y,ey) as i4) ::
     GLet (z,ez) :: c when
         check_ddh a b ex ey ez c ju.ju_ev ->
    [{ju with ju_gdef =
        i1 :: i2:: GSamp(vsc,(mk_Fq,[])) :: 
          i3 :: i4 :: GLet(z,mk_GExp mk_GGen vc) :: c }]
  | _ -> failwith "can not apply ddh"

(* Bad rule, random oracle *)
let rbad p vsx ju =
  assert_no_occur vsx ju "rbad";
  match get_ju_ctxt ju p with
  | GLet(vs,e'), ctxt when is_H e' ->
    let h,e = destr_H e' in
    (* TODO CHECK THAT h is only used here *)
    let i = [GSamp(vs,(e'.e_ty,[]))] in
    let ju1 = set_ju_ctxt i ctxt in
    let vx = mk_V vsx in
    let ev = mk_ElemH e vx [vsx,h] in
    let ju2 = { ju1 with ju_ev = ev } in
    [ju1;ju2]
  | _ -> 
    failwith "can not apply bad rule"
    
(* Bilinear decisional diffie-helman *)
let check_bddh a b c ex ey ez eU _C ev =
 let a = mk_V a in
 let b = mk_V b in
 let c = mk_V c in
 let r = Se.union (read_gcmds _C) (e_vars ev) in
 ty_equal a.e_ty mk_Fq &&
   ty_equal b.e_ty mk_Fq &&
   ty_equal c.e_ty mk_Fq &&
   e_equal ex (mk_GExp mk_GGen a) &&
   e_equal ey (mk_GExp mk_GGen b) &&
   e_equal ez (mk_GExp mk_GGen c) &&
   e_equal eU (mk_GTExp mk_GTGen (mk_FMult [mk_FMult [a;b]; c])) &&
   not (Se.mem a r) && not (Se.mem b r) && not (Se.mem c r) &&
   not (has_log_gcmds _C) && not (has_log ev) 

let rbddh vsu ju =
  assert_no_occur vsu ju "rbddh";
  let vu = mk_V vsu in
  match ju.ju_gdef with
  | (GSamp(a,(_ta,[])) as i1) ::
    (GSamp(b,(_tb,[])) as i2) ::
    (GSamp(c,(_tc,[])) as i3) ::
    (GLet (_x,ex) as i4) ::
    (GLet (_y,ey) as i5) ::
    (GLet (_z,ez) as i6)::
    GLet (_U,eU) ::_C when
         check_bddh a b c ex ey ez eU _C ju.ju_ev ->
    [{ju with ju_gdef =
        i1 :: i2:: i3 :: GSamp(vsu,(mk_Fq,[])) :: 
          i4 :: i5 :: i6 :: GLet(_U,mk_GTExp mk_GTGen vu) :: _C }]
  | _ -> failwith "can not apply bddh"
