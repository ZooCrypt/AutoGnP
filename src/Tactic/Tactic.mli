(** Tactic engine: transformations of proof states. *)

open Proofstate
open Game
open Format
open Expr
open Type
open ParserUtil

(* val fail_unless : (unit -> bool) -> string -> unit *)

val create_var : bool -> proofstate -> string -> ty -> Vsym.t

val invert_ctxt : Vsym.t * expr -> Vsym.t * expr

val handle_tactic : proofstate -> tactic -> judgment list -> proofstate

val pp_goals : formatter -> judgment list option -> unit

val handle_instr : proofstate -> instr -> proofstate * string

val eval_theory : string -> proofstate
