(** Interface to computer algebra systems Singular and Macaulay. *)


val mod_reduce : Expr.expr -> Expr.expr -> bool

(* (inv, xor) list *)
val solve_xor : (Expr.expr * Expr.expr) list -> Expr.expr -> Expr.expr

val norm : (Expr.expr -> Expr.expr) -> Expr.expr -> Expr.expr 


