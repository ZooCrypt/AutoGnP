(*s Deducibility of expressions. *)

(*i*)
open Expr
(*i*)

val invert : ?ppt_inverter:bool -> (expr * inverter) list -> expr -> expr
