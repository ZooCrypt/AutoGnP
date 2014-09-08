(*s fixme *)

open Nondet
open Syms
open Expr
open CoreRules
open TheoryState
open ParserUtil

val t_rnd_maybe :
  theory_state ->  Game.gcmd_pos option
  -> (string * parse_expr) option -> (string * parse_expr) option
  -> goal -> proof_state nondet

val t_random_indep : CoreRules.tactic

val invert_ctxt : Vsym.t * expr -> Vsym.t * expr

