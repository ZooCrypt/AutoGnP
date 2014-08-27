(** Decisional and computational assumptions. *)

(** Decisional assumptions. *)
type assumption_decision = private
  { ad_name     : string;
    ad_prefix1  : Game.gdef;
    ad_prefix2  : Game.gdef;
    ad_pubvars  : Vsym.S.t;
    ad_privvars : Vsym.S.t; 
  }

val mk_ad : string -> Game.gdef -> Game.gdef -> Vsym.S.t -> assumption_decision

val needed_var : Util.direction  -> assumption_decision -> Vsym.t list

val subst : Vsym.t Vsym.M.t -> assumption_decision -> assumption_decision

(** Computational assumptions. *)
type assumption_computational =
  { ac_name       : string;
    ac_prefix     : Game.gdef;
    ac_event_var  : Vsym.t;
    ac_event      : Expr.expr;
    ac_pubvars    : Vsym.S.t;
    ac_privvars   : Vsym.S.t;
  }

val mk_ac :
  string -> Game.gdef -> Vsym.t -> Expr.expr -> Vsym.S.t -> assumption_computational

val instantiate : Vsym.t Vsym.M.t -> assumption_computational -> assumption_computational
