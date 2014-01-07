(** Interface to computer algebra systems Singular and Macaulay. *)
val norm : (Expr.expr -> Expr.expr) -> Expr.expr -> Expr.expr

val mod_reduce : Expr.expr -> Expr.expr -> bool