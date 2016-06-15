(* Grobner basis computations for K[X]-module *)

open NormField

type pol

       
val groebner : (pol*int list) list ->  (pol*int list) list

val is_in :  (pol*int list) list -> pol -> bool

val eps_to_polys : EP.t list -> pol list * int list * (int, Expr.expr) Hashtbl.t

                                                                       
val polys_to_eps :  pol list ->  int list -> (int, Expr.expr) Hashtbl.t -> Expr.expr list

