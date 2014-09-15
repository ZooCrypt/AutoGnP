(*s Logical rules built on top of core rules. *)

open Util
open Type
open Syms
open Expr
open Game
open CoreRules

val ( @> ) : tactic -> tactic -> tactic
val ( @>= ) : 'a rtactic -> ('a -> tactic) -> tactic
val ( @>>= ) : 'a rtactic -> ('a -> 'b rtactic) -> 'b rtactic
val ( @| ) : tactic -> tactic -> tactic
val ( @|| ) : tactic -> tactic -> tactic

type dir = ToFront | ToEnd

val vars_dexc : Vsym.t -> Expr.expr list -> Expr.Se.t

val parallel_swaps : (int * int) list -> (int * int) list

val t_swap_max : dir -> gcmd_pos -> Se.t -> int rtactic

val t_swap_others_max : dir -> gcmd_pos -> int rtactic

val samplings : gcmd list -> (gcmd_pos * (vs * (ty * expr list))) list

val pp_samp : F.formatter -> gcmd_pos * (vs * (ty * expr list)) -> unit

val osamplings : gcmd list -> (ocmd_pos * (vs * (ty * expr list))) list

val pp_osamp : F.formatter -> ocmd_pos * (vs * (ty * expr list)) -> unit

val oguards : gcmd list -> (ocmd_pos * expr) list

val lets :  gcmd list -> (int * (vs * expr)) list

val pp_let : F.formatter -> int * (vs * expr) -> unit

val t_seq_list : tactic list -> tactic

val t_or_list : tactic list -> tactic

val t_print : string -> tactic

val t_debug : string -> tactic

val t_guard : (goal -> bool) -> tactic

val pp_proof_tree : bool -> Util.F.formatter -> CoreRules.proof_tree -> unit

val simplify_proof_tree : proof_tree -> proof_tree

val prove_by_admit: string -> proof_state -> proof_state
