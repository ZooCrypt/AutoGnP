(*s Derived rules for dealing with random samplings. *)

(*i*)
open TheoryTypes
open ParserTypes
(*i*)

val t_rnd_maybe :
  ?i_rvars:Syms.Vsym.S.t
  -> theory_state
  -> bool
  -> Game.gcmd_pos option
  -> parse_ctx option
  -> parse_ctx option
  -> Expr.expr option
  -> CoreRules.tactic

val t_rnd_oracle_maybe :
  ?i_rvars:Syms.Vsym.S.t
  -> theory_state
  -> Game.ocmd_pos option
  -> parse_ctx option
  -> parse_ctx option
  -> CoreRules.tactic
