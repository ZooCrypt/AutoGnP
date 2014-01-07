(** Logical rules built on top of core rules. *)

open Game
open Assumption
open Expr

val rnorm : judgment -> judgment list

val rnorm_nounfold : judgment -> judgment list

val runfold_only : judgment -> judgment list

val rnorm_unknown : expr list -> judgment -> judgment list

val rlet_abstract : int -> Vsym.t -> expr -> judgment -> judgment list

val rlet_unfold : int -> judgment -> judgment list

val rassm : Util.direction -> assumption_decision -> Vsym.t Vsym.M.t -> judgment -> judgment list
