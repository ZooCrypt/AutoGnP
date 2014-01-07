(** Normed field expressions and polynomials. *)

open Expr

val is_norm_field_exp : 'a gexpr -> bool

type var = int

type 'a monom = ('a * int) list

type coeff = int

type 'a poly = (coeff * 'a monom) list

val map_poly : ('a -> 'b) -> 'a poly -> 'b poly

val exp_of_poly : expr poly -> expr

val polys_of_field_expr : expr -> expr poly * (expr poly) option

val factor_out : expr -> expr poly -> expr poly * expr poly