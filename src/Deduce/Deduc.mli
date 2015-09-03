(*s Deducibility of expressions. *)

(*i*)
open Expr
open ExprUtils
open TheoryTypes
(*i*)

val invert : ?ppt_inverter:bool -> theory_state -> (expr * inverter) list -> expr -> expr
