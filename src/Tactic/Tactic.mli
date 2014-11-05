(*s Tactic engine: transformations of proof states. *)

open TheoryState
open Game
open Util
open ParserUtil

(*i val pp_goals : formatter -> CoreRules.goals option -> unit i*)
val pp_jus   : int -> F.formatter -> judgment list -> unit
val handle_instr : bool -> theory_state -> instr -> theory_state * string

val eval_theory : string -> theory_state
