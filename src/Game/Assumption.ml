open Game
open Expr
open Wf

type assumption_decision =
  { ad_prefix1    : gdef;
    ad_prefix2    : gdef;
    ad_privvars   : Vsym.S.t; 
  }

let mk_ad pref1 pref2 pvars =
  let check_nocall gd =
    List.for_all
      (function GCall _ -> false | _ -> true)
      gd
  in
  let pvarse =
    Vsym.S.fold (fun x acc -> Se.add (mk_V x) acc)
      pvars Se.empty
  in
  (* FIXME: check that groupvars(pref1) = groupvars(pref2) *)
  assert (check_nocall pref1);
  assert (check_nocall pref2);
  ignore (wf_gdef pref1);
  ignore (wf_gdef pref2);
  assert (Se.equal
           (Se.diff (gdef_vars pref1) pvarse)
           (Se.diff (gdef_vars pref2) pvarse));
  
  { ad_prefix1    = pref1;
    ad_prefix2    = pref2;
    ad_privvars   = pvars;
  }

let needed_var dir assm = 
  let toSym se =
    Se.fold (fun e s -> Vsym.S.add (destr_V e) s)
      se Vsym.S.empty in
  let w1 = toSym(write_gcmds assm.ad_prefix1) in
  let w2 = toSym(write_gcmds assm.ad_prefix2) in
  if dir = `LtoR then Vsym.S.elements (Vsym.S.diff w2 w1)
  else Vsym.S.elements (Vsym.S.diff w1 w2)

let subst subst assm = 
  let subst_v (x:Vsym.t) = try Vsym.M.find x subst with Not_found -> x in
  let subst_g = Game.subst_v_gdef subst_v in
  { ad_prefix1 = subst_g assm.ad_prefix1;
    ad_prefix2 = subst_g assm.ad_prefix2;
    ad_privvars = 
      Vsym.S.fold (fun x -> Vsym.S.add (subst_v x))
        assm.ad_privvars Vsym.S.empty }

