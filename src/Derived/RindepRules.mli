(* * Derived rules for dealing with random independence. *)

open CoreTactic
open TheoryTypes

val t_random_indep : theory_state -> bool -> tactic
