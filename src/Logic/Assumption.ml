open Game
open Expr
open Wf
open Util

type assumption_decision =
  { ad_name       : string;
    ad_prefix1    : gdef;
    ad_prefix2    : gdef;
    ad_pubvars    : Vsym.S.t;
    ad_privvars   : Vsym.S.t; 
  }

let mk_ad name pref1 pref2 pvars =
  let check_nocall gd =
    List.iter 
      (function
      | GCall (_,f,_,_) -> 
        tacerror "can not use call %a in assumption" Asym.pp f
      | _ -> ())
      gd
  in
  let pvarse =
    Vsym.S.fold (fun x acc -> Se.add (mk_V x) acc)
      pvars Se.empty
  in
  (* FIXME: check that groupvars(pref1) = groupvars(pref2) *)
  check_nocall pref1;
  check_nocall pref2;
  ignore (wf_gdef NoCheckDivZero pref1);
  ignore (wf_gdef NoCheckDivZero pref2);
  let pubvar1 = Se.diff (gdef_vars pref1) pvarse in
  let pubvar2 = Se.diff (gdef_vars pref2) pvarse in
  if not (Se.equal pubvar1 pubvar2) then begin
    let diff = Se.union (Se.diff pubvar1 pubvar2) (Se.diff pubvar2 pubvar1) in
    tacerror "public variables should be equal: %a"
      (pp_list "@ " pp_exp) (Se.elements diff)
  end;
  let pubvars = 
    Se.fold (fun e s -> Vsym.S.add (destr_V e) s) pubvar1 Vsym.S.empty in
  { ad_name = name;
    ad_prefix1    = pref1;
    ad_prefix2    = pref2;
    ad_pubvars    = pubvars;
    ad_privvars   = pvars;
  }

let needed_var dir assm = 
  let toSym se =
    Se.fold (fun e s -> Vsym.S.add (destr_V e) s)
      se Vsym.S.empty in
  let w1 = toSym(write_gcmds assm.ad_prefix1) in
  let w2 = toSym(write_gcmds assm.ad_prefix2) in
  if dir = LeftToRight then Vsym.S.elements (Vsym.S.diff w2 w1)
  else Vsym.S.elements (Vsym.S.diff w1 w2)

let subst subst assm = 
  let subst_v (x:Vsym.t) = try Vsym.M.find x subst with Not_found -> x in
  let subst_s s =
    Vsym.S.fold (fun x -> Vsym.S.add (subst_v x)) s Vsym.S.empty in
  let subst_g = Game.subst_v_gdef subst_v in
  { ad_name     = assm.ad_name;
    ad_prefix1  = subst_g assm.ad_prefix1;
    ad_prefix2  = subst_g assm.ad_prefix2;
    ad_pubvars  = subst_s assm.ad_pubvars;
    ad_privvars = subst_s assm.ad_privvars;
  }
