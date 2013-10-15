open Util
open Type
open Expr
open Game


(* ----------------------------------------------------------------------- *)
(** {1 Rules and tactic language} *)

(** goal handling *)

let apply rule goals = match goals with
  | g::gs -> rule g @ gs
  | _ -> failwith "there are no goals"

let delay goals = match goals with
  | g::gs -> gs@[g]
  | []    -> []

(* ----------------------------------------------------------------------- *)
(** {2 Low level rule} *)

(** Conversion *)

let check_conv ju1 ju2 = 
  ju_equal (norm_ju ju1) (norm_ju ju2) 

let rconv new_ju1 ju1 = 

  Format.printf "Check conv@.ju = %a@." pp_ju ju1; 
  Format.printf "new_ju = %a@." pp_ju new_ju1; 
  let ju = norm_ju ju1 in
  let new_ju = norm_ju new_ju1 in
  Format.printf "Check conv@.ju = %a@." pp_ju ju1; 
  Format.printf "new_ju = %a@." pp_ju new_ju1; 
  Format.printf "norm ju = %a@." pp_ju ju;
  Format.printf "norm new_ju = %a@." pp_ju new_ju; 
  if not (ju_equal ju new_ju) then
    (  
      Format.printf "ju = %a@.new_ju = %a@." 
        pp_ju ju pp_ju new_ju;
      let cc = List.combine ju.ju_gdef new_ju.ju_gdef in
      (try
         let (i1,i2) = List.find (fun (i1,i2) -> not (gc_equal i1 i2)) cc in
         Format.printf "i1 = %a@.i2 = %a@." pp_gcmd i1 pp_gcmd i2
       with _ -> Format.printf "????@."); 
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
let rrandom p c1 c2 ju =
  match get_ju_ctxt ju p with
  | GSamp(vs,((t,[]) as d)), ctxt ->
    let v = mk_V vs in
    ensure_bijection c1 c2 v; (* FIXME: check that both contexts well-defined at given position *)
    let vs' = Vsym.mk (Id.name vs.Vsym.id) t in
    let cmds = [ GSamp(vs',d);
                 GLet(vs, inst_ctxt c1 (mk_V vs')) ]
    in
    [ set_ju_ctxt cmds ctxt]
  | _ -> failwith "random: position given is not a sampling"

(* random in oracle *)
let rrandom_oracle p c1 c2 ju =
  match get_ju_octxt ju p with
  | LSamp(vs,((t,[]) as d)), ctxt ->
    let v = mk_V vs in
    ensure_bijection c1 c2 v; (* FIXME: check that both contexts well-defined at given position *)
    let vs' = Vsym.mk (Id.name vs.Vsym.id) t in
    let cmds = [ LSamp(vs',d);
                 LLet(vs, inst_ctxt c1 (mk_V vs')) ]
    in
    [ set_ju_octxt cmds ctxt]
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
    let i,(hd,tl,e) = get_ju_ctxt ju i in
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
    set_ju_ctxt c2 (c1,c3,e)

let rswap i delta ju = [swap i delta ju]

let swap_oracle i delta ju = 
  if delta = 0 then ju
  else
    let i,(((hd,tl), odecl, call), ctxt) = get_ju_octxt ju i in
    let c1,c2,c3 = 
      if delta < 0 then
        let hhd,thd = cut_n delta hd in
        thd,hhd,tl
      else 
        let htl, ttl = cut_n delta tl in
        hd, List.rev htl, ttl in
    check_swap read_lcmds write_lcmds i c2;
    let c2, c3 = 
      if delta > 0 then c2, i::c3 else i::c2, c3 in
    set_ju_octxt c2 (((c1,c3),odecl,call),ctxt)

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

let rddh vc ju = 
  match ju.ju_gdef with
  | (GSamp(a,(_ta,[])) as i1) ::
    (GSamp(b,(_tb,[])) as i2) ::
    (GLet (_x,ex) as i3) ::
    (GLet (_y,ey) as i4) ::
     GLet (z,ez) :: c when
         check_ddh a b ex ey ez c ju.ju_ev ->
    let vc = Vsym.mk vc mk_Fq in
    [{ju with ju_gdef =
        i1 :: i2:: GSamp(vc,(mk_Fq,[])) :: 
          i3 :: i4 :: GLet(z,mk_GExp mk_GGen (mk_V vc)) :: c }]
  | _ -> failwith "can not apply ddh"



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
   e_equal eU (mk_GTExp mk_GTGen (mk_FMult [a;b;c])) &&
   not (Se.mem a r) && not (Se.mem b r) && not (Se.mem c r) &&
   not (has_log_gcmds _C) && not (has_log ev) 

let rbddh vu ju =
  match ju.ju_gdef with
  | (GSamp(a,(_ta,[])) as i1) ::
    (GSamp(b,(_tb,[])) as i2) ::
    (GSamp(c,(_tc,[])) as i3) ::
    (GLet (_x,ex) as i4) ::
    (GLet (_y,ey) as i5) ::
    (GLet (_z,ez) as i6)::
    GLet (_U,eU) ::_C when
         check_bddh a b c ex ey ez eU _C ju.ju_ev ->
    let vu = Vsym.mk vu mk_Fq in
    [{ju with ju_gdef =
        i1 :: i2:: i3 :: GSamp(vu,(mk_Fq,[])) :: 
          i4 :: i5 :: i6 :: GLet(_U,mk_GTExp mk_GTGen (mk_V vu)) :: _C }]
  | _ -> failwith "can not apply bddh"
