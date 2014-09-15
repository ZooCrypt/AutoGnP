(*s Deducibility for field expressions. *)

(*i*)
open Syms
open Expr
(*i*)

(** [solve_fq ecs e] tries to compute a field context that
    deduces [e] from [List.map snd es] and returns the
    context assuming that [List.map fst es] are the contexts
    for these known terms. *)
val solve_fq : (expr * inverter) list -> expr -> inverter


val solve_fq_vars_known : expr -> Vsym.t  -> expr
