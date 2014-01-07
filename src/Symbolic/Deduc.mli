(** Deducibility of expressions. *)

open Expr

val invert : (expr * expr) list -> expr -> expr
