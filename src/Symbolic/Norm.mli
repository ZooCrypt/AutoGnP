(*s Normal form computation for expressions. *)

(*i*)
open Expr
(*i*)

(** [norm_expr e] computes the normal form of the expression [e], if strong is true,
    then and will be sorted and equations a = b will be simplified to a - b = 0. *)
val norm_expr_weak : expr -> expr
val norm_expr_strong : expr -> expr

val norm_expr_abbrev_weak : expr -> expr
val norm_expr_abbrev_strong : expr -> expr

val norm_expr_nice : expr -> expr

val remove_tuple_proj : expr -> expr

(** [abbrev_ggen e] simplifies the expression [e] (e.g. for printing)
    by replacing [g^1] with [g] and [g^log(A)] with [A]. *)
val abbrev_ggen : expr -> expr

(** [e_equalmod e1 e2] returns [true] if [e1] and [e2] are equal modulo
    the equational theory. *)
val e_equalmod : expr -> expr -> bool
