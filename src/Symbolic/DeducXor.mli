(*s Deducibility of Xor expressions. *)

(*i*)
open Expr
(*i*)

(** [solve_xor ecs e] tries to compute an xor context that
    deduces [e] from [List.map snd es] and returns the
    context assuming that [List.map fst es] are the contexts
    for these known terms. *)
val solve_xor : (expr * expr) list -> expr -> expr
