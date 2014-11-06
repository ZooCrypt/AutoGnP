(*s Deducibility of expressions. *)

(*i*)
open Expr
open ExprUtils
(*i*)

val invert : ?ppt_inverter:bool -> (expr * inverter) list -> expr -> expr
