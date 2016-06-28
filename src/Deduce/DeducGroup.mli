(* * Deducibility for group expressions. *)

open Syms
open Expr
open ExprUtils

val solve_group :      ?rnd_vars:(Expr.He.key * Expr.He.key list) list ->
           ?mult_secrets:Expr.expr list -> EmapSym.t list -> (expr * inverter) list -> expr -> inverter
