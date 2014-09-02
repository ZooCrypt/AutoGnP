(*s Logical rules built on top of core rules. *)

open Assumption
open Util
open Expr
open CoreRules
open Syms

val ( @. ) : tactic -> tactic -> tactic
val ( @+ ) : tactic -> tactic list -> tactic
val ( @| ) : tactic -> tactic -> tactic

val t_norm : tactic

val t_norm_nounfold : tactic

val t_unfold_only : tactic 

val t_norm_unknown : expr list -> tactic

val t_let_abstract : int -> Vsym.t -> expr -> tactic 

val t_let_unfold : int -> tactic

val t_assm_dec : direction -> assm_dec -> Vsym.t Vsym.M.t -> tactic

val t_assm_comp : assm_comp -> expr -> tactic

val t_random_indep : tactic

val invert_ctxt : Syms.Vsym.t * Expr.expr -> Syms.Vsym.t * Expr.expr
