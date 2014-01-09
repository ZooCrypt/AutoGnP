(** Normal form computation for expressions. *)

open Expr

(** [norm_expr e] computes the normal form of the expression [e]. *)
val norm_expr : expr -> expr

val remove_tuple_proj : expr -> expr

(** [abbrev_ggen e] simplifies the expression [e] (e.g. for printing)
    by replacing [g^1] with [g] and [g^log(A)] with [A]. *)
val abbrev_ggen : expr -> expr

(** [e_equalmod e1 e2] returns [true] if [e1] and [e2] are equal modulo
    the equational theory. *)
val e_equalmod : expr -> expr -> bool
