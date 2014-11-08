(*s Automated derived rules *)

(*i*)
open CoreRules
open TheoryTypes
(*i*)

val t_simp : bool -> int -> theory_state -> tactic

val t_ctx_ev_maybe : int option -> tactic
     
