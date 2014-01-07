(** Interface to computer algebra systems Singular and Macaulay. *)

open Expr

val norm : (expr -> expr) -> expr -> expr

val mod_reduce : expr -> expr -> bool