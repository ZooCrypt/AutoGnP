(** Computational assumptions. *)
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
