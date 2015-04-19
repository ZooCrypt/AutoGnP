(*s Deducibility for group expressions. *)

(*i*)
open Syms
open Expr
open ExprUtils
(*i*)

val solve_group : Esym.t list -> (expr * inverter) list -> expr -> inverter
