open Game
open Expr
open Wf
open Util

(* ----------------------------------------------------------------------- *)
(** {1 Decisional assumptions} *)

type assumption_decision =
  { ad_name       : string;
    ad_prefix1    : gdef;
    ad_prefix2    : gdef;
    ad_pubvars    : Vsym.S.t;
    ad_privvars   : Vsym.S.t; 
  }

let check_nocall gd =
  List.iter 
    (function
    | GCall (_,f,_,_) -> 
      tacerror "can not use call %a in assumption" Asym.pp f
    | _ -> ())
    gd

let mk_ad name pref1 pref2 pvars =
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

(* ----------------------------------------------------------------------- *)
(** {2 Computational assumptions} *)

type assumption_computational =
  { ac_name       : string;
    ac_prefix     : gdef;
    ac_event_var  : Vsym.t;
    ac_event      : expr;
    ac_pubvars    : Vsym.S.t;
    ac_privvars   : Vsym.S.t;
  }

let mk_ac name pref ev_var ev priv_vars =
  let priv_varse =
    Vsym.S.fold (fun x acc -> Se.add (mk_V x) acc) priv_vars Se.empty
  in
  check_nocall pref;
  ignore (wf_gdef NoCheckDivZero pref);
  let pub_varse = Se.diff (gdef_vars pref) priv_varse in
  let pub_vars =
    Se.fold (fun e s -> Vsym.S.add (destr_V e) s) pub_varse Vsym.S.empty
  in
  (* check that all variables in event defined in gdef + ev_var *)
  { ac_name       = name;
    ac_prefix     = pref;
    ac_event_var  = ev_var;
    ac_event      = ev;
    ac_pubvars    = pub_vars;
    ac_privvars   = priv_vars;
  }

let instantiate subst assm = 
  let subst_v (x:Vsym.t) = try Vsym.M.find x subst with Not_found -> x in
  let subst_s s =
    Vsym.S.fold (fun x -> Vsym.S.add (subst_v x)) s Vsym.S.empty in
  let subst_g = Game.subst_v_gdef subst_v in
  { ac_name       = assm.ac_name;
    ac_prefix     = subst_g assm.ac_prefix;
    ac_event_var  = assm.ac_event_var;
    ac_event      = subst_v_e subst_v assm.ac_event;
    ac_pubvars    = subst_s assm.ac_pubvars;
    ac_privvars   = subst_s assm.ac_privvars;
  }
