(*s Decisional and computational assumptions. *)

(*i*)
open Syms
(*i*)

(** Decisional assumptions. *)
type assm_dec = private
  { ad_name     : string;
    ad_prefix1  : Game.gdef;
    ad_prefix2  : Game.gdef;
    ad_pubvars  : Vsym.S.t;
    ad_privvars : Vsym.S.t; 
  }

val mk_assm_dec : string -> Game.gdef -> Game.gdef -> Vsym.S.t -> assm_dec

val needed_var : Util.direction  -> assm_dec -> Vsym.t list

val ad_subst : Vsym.t Vsym.M.t -> assm_dec -> assm_dec

(** Computational assumptions. *)
type assm_comp = private
  { ac_name       : string;
    ac_prefix     : Game.gdef;
    ac_event_var  : Vsym.t;
    ac_event      : Expr.expr;
    ac_pubvars    : Vsym.S.t;
    ac_privvars   : Vsym.S.t;
  }

val mk_assm_comp :
  string -> Game.gdef -> Vsym.t -> Expr.expr -> Vsym.S.t -> assm_comp

val instantiate : Vsym.t Vsym.M.t -> assm_comp -> assm_comp
