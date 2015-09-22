(* * Deducibility for group expressions. *)

open Syms
open Expr
open ExprUtils

val solve_group : Esym.t list -> (expr * inverter) list -> expr -> inverter
