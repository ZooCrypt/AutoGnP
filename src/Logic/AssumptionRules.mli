open Util
open Expr
open Assumption
open CoreRules
open TheoryState

val t_assm_dec :
  theory_state -> string option -> direction option -> (string list) option -> tactic

val t_assm_comp : assm_comp -> expr -> tactic
