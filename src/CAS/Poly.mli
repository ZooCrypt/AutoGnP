(** Normed field expressions and polynomials. *)

open Expr

(** [is_norm_field_exp e] returns true if
    [e] is in normal-form as a field expression.
    The function only considers the outermost
    field context. *)
val is_norm_field_exp : 'a gexpr -> bool

type 'a monom = ('a * int) list

type coeff = int

type 'a poly = (coeff * 'a monom) list

(** [map_poly f p] maps the function [f] over all
    variables of [p]. *)
val map_poly : ('a -> 'b) -> 'a poly -> 'b poly

(** [exp_of_poly p] converts the polynomial p to an expression. *)
val exp_of_poly : expr poly -> expr

(** [polys_of_field_expr e] converts a field expression [e] in 
    normal-form into the numerator polynomial and (if nontrivial)
    the denominator polynomial. *)
val polys_of_field_expr : expr -> expr poly * (expr poly) option

(** [factor_out e p] tries to represent the polynomial
    [p] as [f + e*g] where [f] and [g] do not contain
    the variable [e], if possible. It returns [g] as the
    first list and [f] as the second list. *)
val factor_out : expr -> expr poly -> expr poly * expr poly
