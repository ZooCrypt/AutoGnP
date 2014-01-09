(** Tactic engine: transformations of proof states. *)

open Proofstate
open Game
open Format
open Expr
open Type
open ParserUtil

val pp_goals : formatter -> CoreRules.goals option -> unit
val pp_jus   : formatter -> judgment list option -> unit
val handle_instr : proofstate -> instr -> proofstate * string

val eval_theory : string -> proofstate
