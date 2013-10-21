type assumption_decision = private
  { ad_prefix1  : Game.gdef;
    ad_prefix2  : Game.gdef;
    ad_privvars : Vsym.S.t; 
  }

val mk_ad : Game.gdef -> Game.gdef -> Vsym.S.t -> assumption_decision

val needed_var : [`LtoR | `RtoL] -> assumption_decision -> Vsym.t list

val subst : Vsym.t Vsym.M.t -> assumption_decision -> assumption_decision
