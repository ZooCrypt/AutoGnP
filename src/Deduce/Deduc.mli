(* * Deducibility of expressions. *)

open Expr
open ExprUtils
open TheoryTypes

val invert : ?rnd_deduce_enable:bool -> ?ppt_inverter:bool -> theory_state -> (expr * inverter) list -> expr -> inverter
