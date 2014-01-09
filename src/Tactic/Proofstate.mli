(** Goals and mappings from strings to variables/symbols. *)

open Type
open Game

type proofstate = {
  ps_lvars : (string, Lenvar.id) Hashtbl.t;
  ps_gvars : (string, Groupvar.id) Hashtbl.t;
  ps_rodecls : (string, Hsym.t) Hashtbl.t;
  ps_odecls : (string, Osym.t) Hashtbl.t;
  ps_adecls : (string, Asym.t) Hashtbl.t;
  ps_emdecls : (string, Esym.t) Hashtbl.t;
  ps_assms : (string, Assumption.assumption_decision) Hashtbl.t;
  ps_vars : (string, Vsym.t) Hashtbl.t;
  ps_goals : CoreRules.goals option;
}

val mk_ps : unit -> proofstate

val ps_copy : proofstate -> proofstate

val ps_resetvars : proofstate -> proofstate

val create_lenvar : proofstate -> string -> Lenvar.id

val create_groupvar : proofstate -> string -> Groupvar.id

val create_var : bool -> proofstate -> string -> Type.ty -> Vsym.t option

val create_var_reuse : proofstate -> string -> Type.ty -> Vsym.t
