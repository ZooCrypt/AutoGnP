(*s Decisional and computational assumptions *)

(*i*)
open Game
open Expr
open Wf
open Util
open Syms
open Gsyms
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Decisional assumptions} *)

type assm_dec =
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

let mk_assm_dec name pref1 pref2 pvars =
  check_nocall pref1;
  check_nocall pref2;
  ignore (wf_gdef NoCheckDivZero pref1);
  ignore (wf_gdef NoCheckDivZero pref2);
  let pubvar1 = Vsym.S.diff (gdef_all_vars pref1) pvars in
  let pubvar2 = Vsym.S.diff (gdef_all_vars pref2) pvars in
  if not (Vsym.S.equal pubvar1 pubvar2) then begin
    let diff = Vsym.S.union (Vsym.S.diff pubvar1 pubvar2) (Vsym.S.diff pubvar2 pubvar1) in
    tacerror "public variables should be equal: %a"
      (pp_list "@ " Vsym.pp) (Vsym.S.elements diff)
  end;
  { ad_name = name;
    ad_prefix1    = pref1;
    ad_prefix2    = pref2;
    ad_pubvars    = pubvar1;
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

let ad_subst subst assm =
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

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Computational assumptions} *)

type assm_comp =
  { ac_name       : string;
    ac_prefix     : gdef;
    ac_event_var  : Vsym.t;
    ac_event      : expr;
    ac_pubvars    : Vsym.S.t;
    ac_privvars   : Vsym.S.t;
  }

let mk_assm_comp name pref ev_var ev priv_vars =
  check_nocall pref;
  ignore (wf_gdef NoCheckDivZero pref);
  let pub_vars = Vsym.S.diff (gdef_all_vars pref) priv_vars in
  (* check that all variables in event defined in $gdef + ev_var$ *)
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
    Vsym.S.fold (fun x -> Vsym.S.add (subst_v x)) s Vsym.S.empty
  in
  let subst_g = Game.subst_v_gdef subst_v in
  { ac_name       = assm.ac_name;
    ac_prefix     = subst_g assm.ac_prefix;
    ac_event_var  = assm.ac_event_var;
    ac_event      = subst_v_e subst_v assm.ac_event;
    ac_pubvars    = subst_s assm.ac_pubvars;
    ac_privvars   = subst_s assm.ac_privvars;
  }
