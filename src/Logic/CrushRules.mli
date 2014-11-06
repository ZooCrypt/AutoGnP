(*s Automated derived rules *)

(*i*)
open CoreRules
open TheoryTypes
(*i*)

val t_simp : bool -> int -> theory_state -> tactic

val t_crush : bool -> int option -> theory_state -> proof_state -> tactic
     
