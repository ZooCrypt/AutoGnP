(** Normed field expressions. *)

val is_norm_field_exp : 'a Expr.gexpr -> bool

val is_fe0 : 'a Expr.gexpr -> bool

val is_mon : 'a Expr.gexpr -> bool

val is_mon0 : 'a Expr.gexpr -> bool

type var = int

type 'a monom = ('a * int) list

type coeff = int

type 'a poly = (coeff * 'a monom) list

val map_poly : ('a -> 'b) -> ('c * ('a * 'd) list) list -> ('c * ('b * 'd) list) list

val exps_of_monom : Expr.expr monom -> Expr.expr list

val exp_of_poly : (int * Expr.expr monom) list -> Expr.expr

val polys_of_field_expr :
  'a Expr.gexpr ->
  (int * ('a Expr.gexpr * int) list) list *
  (int * ('a Expr.gexpr * int) list) list option

val factor_out :
  Expr.expr ->
  ('a * (Expr.expr * int) list) list ->
  ('a * (Expr.expr * int) list) list * ('a * (Expr.expr * int) list) list
