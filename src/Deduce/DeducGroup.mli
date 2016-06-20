(* * Deducibility for group expressions. *)

open Syms
open Expr
open ExprUtils

val solve_group :  ?mult_secrets:'a list -> EmapSym.t list -> (expr * inverter) list -> expr -> inverter
