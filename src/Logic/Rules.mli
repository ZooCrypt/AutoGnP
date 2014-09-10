(*s Logical rules built on top of core rules. *)

open CoreRules
open Game
open Type
open Expr
open Util

val ( @> ) : tactic -> tactic -> tactic
val ( @>= ) : 'a rtactic -> ('a -> tactic) -> tactic
val ( @>>= ) : 'a rtactic -> ('a -> 'b rtactic) -> 'b rtactic
(* val ( @+ ) : tactic -> tactic list -> tactic *)
val ( @| ) : tactic -> tactic -> tactic
val ( @|| ) : tactic -> tactic -> tactic

type dir = ToFront | ToEnd

val vars_dexc : Syms.Vsym.t -> Expr.expr list -> Expr.Se.t

val t_swap_max : dir -> gcmd_pos -> Se.t -> int rtactic

val t_swap_others_max : dir -> gcmd_pos -> int rtactic

val mk_name : unit -> string

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

val pp_proof_tree : Util.F.formatter -> CoreRules.proof_tree -> unit

val simplify_proof_tree : proof_tree -> proof_tree

val prove_by_admit: string -> proof_state -> proof_state
