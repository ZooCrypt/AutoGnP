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

type assm_dec = {
  ad_name       : string;   (*r name of assumption *)
  ad_prefix1    : gdef;     (*r prefix for left *)
  ad_prefix2    : gdef;     (*r prefix for right *)
  ad_pubvars    : Vsym.S.t; (*r public variables *)
  ad_privvars   : Vsym.S.t; (*r private variables *)
  ad_symvars    : vs list list; (*r symmetric in given variables *)
}

let check_nocall gd =
  List.iter 
    (function
    | GCall (_,f,_,_) -> 
      tacerror "can not use call %a in assumption" Asym.pp f
    | _ -> ())
    gd

let mk_assm_dec name pref1 pref2 pvars symvars =
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
    ad_symvars    = symvars;
  }

let needed_var dir assm = 
  let toSym se =
    Se.fold (fun e s -> Vsym.S.add (destr_V e) s)
      se Vsym.S.empty in
  let w1 = toSym(write_gcmds assm.ad_prefix1) in
  let w2 = toSym(write_gcmds assm.ad_prefix2) in
  if dir = LeftToRight then Vsym.S.elements (Vsym.S.diff w2 w1)
  else Vsym.S.elements (Vsym.S.diff w1 w2)

let ad_inst ren assm =
  let ren_v (x:Vsym.t) = try Vsym.M.find x ren with Not_found -> x in
  let ren_s s =
    Vsym.S.fold (fun x -> Vsym.S.add (ren_v x)) s Vsym.S.empty
  in
  let subst_g = Game.subst_v_gdef ren_v in
  { ad_name     = assm.ad_name;
    ad_prefix1  = subst_g assm.ad_prefix1;
    ad_prefix2  = subst_g assm.ad_prefix2;
    ad_pubvars  = ren_s assm.ad_pubvars;
    ad_privvars = ren_s assm.ad_privvars;
    ad_symvars  = L.map (L.map ren_v) assm.ad_symvars;
  }

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Computational assumptions} *)

type assm_comp = {
  ac_name       : string;       (*r name of assumption *)
  ac_prefix     : gdef;         (*r prefix of assumption *)
  ac_event_var  : Vsym.t;       (*r variable in event *)
  ac_event      : Expr.expr;    (*r event expression *)
  ac_pubvars    : Vsym.S.t;     (*r public variables *)
  ac_privvars   : Vsym.S.t;     (*r private variables *)
  ac_symvars    : vs list list; (*r symmetric in given variables *)
}

let mk_assm_comp name pref ev_var ev priv_vars sym_vars =
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
    ac_symvars    = sym_vars;
  }

let ac_inst ren assm =
  let ren_v (x:Vsym.t) = try Vsym.M.find x ren with Not_found -> x in
  let ren_s s =
    Vsym.S.fold (fun x -> Vsym.S.add (ren_v x)) s Vsym.S.empty
  in
  let subst_g = Game.subst_v_gdef ren_v in
  { ac_name       = assm.ac_name;
    ac_prefix     = subst_g assm.ac_prefix;
    ac_event_var  = assm.ac_event_var;
    ac_event      = subst_v_e ren_v assm.ac_event;
    ac_pubvars    = ren_s assm.ac_pubvars;
    ac_privvars   = ren_s assm.ac_privvars;
    ac_symvars    = L.map (L.map ren_v) assm.ac_symvars;
  }
