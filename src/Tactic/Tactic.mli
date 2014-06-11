(** Tactic engine: transformations of proof states. *)

open TheoryState
open Game
open Format
open ParserUtil

(* val pp_goals : formatter -> CoreRules.goals option -> unit *)
val pp_jus   : formatter -> judgment list -> unit
val handle_instr : theory_state -> instr -> theory_state * string

val eval_theory : string -> theory_state
