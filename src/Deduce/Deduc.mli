(* * Deducibility of expressions. *)

open Expr
open ExprUtils
open TheoryTypes

val invert : ?ppt_inverter:bool -> theory_state -> (expr * inverter) list -> expr -> inverter

val rnd_deduce : ?ppt_inverter:bool ->
           Expr.He.key list ->
           TheoryTypes.theory_state ->
           (Expr.expr * ExprUtils.inverter) list ->
           Expr.expr -> ExprUtils.inverter

