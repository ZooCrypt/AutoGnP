(* * Automated derived rules *)

open CoreTactic
open CoreRules
open TheoryTypes

val t_crush : bool -> int option -> theory_state -> proof_state -> tactic
