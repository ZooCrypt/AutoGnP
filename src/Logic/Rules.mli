(*s Logical rules built on top of core rules. *)

(*i*)
open Abbrevs
open Type
open Syms
open Expr
open Game
open CoreRules
(*i*)


(*i ----------------------------------------------------------------------- i*)
(* \hd{Operators for tacticals} *)

val ( @> ) : tactic -> tactic -> tactic
val ( @>> ) : tactic -> tactic list -> tactic
val ( @>= ) : 'a rtactic -> ('a -> tactic) -> tactic
val ( @>>= ) : 'a rtactic -> ('a -> 'b rtactic) -> 'b rtactic
val ( @| ) : tactic -> tactic -> tactic
val ( @|| ) : tactic -> tactic -> tactic

val t_seq_fold : tactic list -> tactic

val t_or_fold : tactic list -> tactic

val t_print : (string lazy_t -> unit) -> string -> tactic

val t_debug : (string lazy_t -> unit) -> string -> tactic

val t_guard : (goal -> bool) -> tactic

(*i ----------------------------------------------------------------------- i*)
(* \hd{Extracting samplings, lets, and guards from game} *)

val samplings : gcmd list -> (gcmd_pos * (vs * (ty * expr list))) list

val osamplings : gcmd list -> (ocmd_pos * (vs * (ty * expr list))) list

val oguards : gcmd list -> (ocmd_pos * expr) list

val lets :  gcmd list -> (int * (vs * expr)) list

(*i ----------------------------------------------------------------------- i*)
(* \hd{Swap maximum amount forward and backward} *)

type dir = ToFront | ToEnd

val vars_dexc : Vsym.t -> Expr.expr list -> Expr.Se.t

val parallel_swaps : (int * int) list -> (int * int) list

val t_swap_max : dir -> gcmd_pos -> Se.t -> int rtactic

val t_swap_others_max : dir -> gcmd_pos -> int rtactic

(*i ----------------------------------------------------------------------- i*)
(* \hd{Simplification and pretty printing} *)

val simplify_proof_tree : proof_tree -> proof_tree

val prove_by_admit : string -> proof_state -> proof_state

val diff_proof_tree : proof_tree * proof_tree -> proof_tree list

val pp_let : F.formatter -> int * (vs * expr) -> unit

val pp_samp : F.formatter -> gcmd_pos * (vs * (ty * expr list)) -> unit

val pp_proof_tree :
  ?hide_admit:bool -> bool -> F.formatter -> CoreRules.proof_tree -> unit

val pp_osamp : F.formatter -> ocmd_pos * (vs * (ty * expr list)) -> unit
