(*s Interface to computer algebra systems Singular, Sage, and Macaulay. *)

open Expr

(** [mod_reduce a b] returns [true] if
    [a mod b = 0] for polynomials [a] and [b].
    The result is undefined if one of the arguments
    is not a polynomial after abstracting away all
    non-field subexpressions. *)
val mod_reduce : expr -> expr -> bool

(** [norm f e] returns the normal-form of [e]
    using [f] recursively to normalize all non-field
    subexpressions. *)
val norm : (expr -> expr) -> expr -> expr 
