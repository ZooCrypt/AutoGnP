(** Normal form computation for expressions. *)
val norm_expr : Expr.expr -> Expr.expr

val abbrev_ggen : Expr.expr -> Expr.expr

val e_equalmod : Expr.expr -> Expr.expr -> bool