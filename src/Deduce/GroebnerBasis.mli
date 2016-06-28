(* Grobner basis computations for K[X]-module *)

open NormField

type mon

type pol
  
type pol_i = mon list * Expr.expr

type i_var_set = int list;;

type frac = pol * pol;;

type frac_r = frac * frac;; 
type gen = frac*i_var_set*bool;;

type basis = gen list;;

type gen_r = frac_r*i_var_set*bool;;

type basis_r = gen_r list;;

       
val groebner : int list -> (int, Expr.expr) Hashtbl.t ->
           (Expr.Me.key * Expr.expr) list ->
           (pol_i * int list) list -> (pol_i * int list) list


val eps_to_polys : (NormField.EP.t * Expr.expr) list ->
           (pol_i) list * int list * (int, Expr.expr) Hashtbl.t

                                                                       
val polys_to_eps :  pol_i list ->
  int list -> (int, Expr.expr) Hashtbl.t -> (Expr.expr * Expr.expr) list

val eps_to_fracs : (NormField.EP.t * Expr.expr) list ->
  (frac) list * int list * (int, Expr.expr) Hashtbl.t

val fracs_to_eps : (pol * pol) list ->
  int list ->
  (int, Expr.expr) Hashtbl.t ->
  (Expr.expr) list

val get_inverter : int list ->
           (int, Expr.expr) Hashtbl.t ->
           (Expr.Me.key * Expr.expr) list ->
           (pol_i * int list) list ->
           pol_i -> bool * Expr.expr

val global_rnd_deduce : (int, Expr.expr) Hashtbl.t ->
  int list ->
  (int * int list) list ->
  int list -> frac list -> frac list -> frac list


