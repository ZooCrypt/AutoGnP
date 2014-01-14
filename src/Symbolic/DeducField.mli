(** Deducibility of Xor expressions. *)
open Expr

(** [solve_fq ecs e] tries to compute a field context that
    deduces [e] from [List.map snd es] and returns the
    context assuming that [List.map fst es] are the contexts
    for these known terms. *)
val solve_fq : (expr * expr) list -> expr -> expr
