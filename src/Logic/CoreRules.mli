

open Game
open Expr
open Assumption
open Util

(** {1 Proofs representation. } *)
type rule_name = 
  | Radmit 
  | Rconv
  | Rctxt_ev   of gcmd_pos * ctxt 
  | Rremove_ev of int list
  | Rmerge_ev  of int * int 
  | Rrandom    of gcmd_pos * ctxt * ctxt * Vsym.t
  | Rrnd_orcl  of ocmd_pos * ctxt * ctxt * Vsym.t
  | Rexcept    of gcmd_pos * expr list
  | Rexc_orcl  of ocmd_pos * expr list 
  | Radd_test  of ocmd_pos * expr * Asym.t * Vsym.t list 
  | Rrw_orcl   of ocmd_pos * direction
  | Rswap      of gcmd_pos * int 
  | Rswap_orcl of ocmd_pos * int 
  | Rrnd_indep of bool * int
  | Rassm_dec  of direction * Vsym.t Vsym.M.t * assumption_decision
  | Rbad       of gcmd_pos * Vsym.t 

type proof_tree = private  
  { dr_subgoal : proof_tree list;
    dr_rule    : rule_name;
    dr_ju      : judgment; }

type rule = judgment -> rule_name * judgment list

type validation = proof_tree list -> proof_tree

type goal = judgment

type goals = {
  subgoals   : judgment list;
  validation : validation
}

type tactic = goal -> goals
type proof_state = goals

exception NoOpenGoal 

(** {2 Basic manipulation tactic}  *)
val get_proof : proof_state -> proof_tree  
val t_first_last : goals -> goals 
val t_on_n : int -> tactic -> goals -> goals
val t_last : tactic -> goals -> goals
val t_first : tactic -> goals -> goals

val t_id : tactic
val t_seq : tactic -> tactic -> tactic
val t_subgoal : tactic list -> goals -> goals

val t_try : tactic -> tactic
val t_or  : tactic -> tactic -> tactic


(** {3 Core rules of the logic. } *)

val radmit : rule
val t_admit : tactic

(** [rconv b j' j] returns [j'] if [j] and [j'] are equal
    after expanding all lets and rewriting with respect
    to the equational theory. *)
val rconv  : bool -> judgment -> rule 
val t_conv : bool -> judgment -> tactic

(** [rctxt_ev ctx i ju] returns the judgment resulting from
    replacing the [i]-th conjunct in the event of [ju]
    with (a) [ctx(a) = ctx(b)] if it is equal to [a = b]
    and (b) [ ctx(a) in \[ ctx(b) | x in l \] ] if it
    is equal to [ a in \[ b | x in l\]]. *)
val rctxt_ev  : int -> ctxt -> rule 
val t_ctxt_ev : int -> ctxt -> tactic

val rremove_ev  : int list -> rule 
val t_remove_ev : int list -> tactic 

val rmerge_ev   : int -> int -> rule
val t_merge_ev  : int -> int -> tactic

(** [rrandom p ctx1 ctx2 v ju] returns the judgment resulting
    from replacing the sampling [r <- d] at position [p]
    with [r <- d; let v = ctx1[r]] and substituting v for r
    in the judgment. The rule checks that [ctx2] is the inverse
    of [ctx1]. *)
val rrandom  : gcmd_pos -> ctxt -> ctxt -> Vsym.t -> rule
val t_random : gcmd_pos -> ctxt -> ctxt -> Vsym.t -> tactic

(** [rrandom p ctx1 ctx2 v ju] returns the judgment resulting
    from replacing the sampling [r <- d] at oracle position [p]
    with [r <- d; let v = ctx1[r]] and substituting v for r
    in the judgment. The rule checks that [ctx2] is the inverse
    of [ctx1]. *)
val rrandom_oracle  : ocmd_pos -> ctxt -> ctxt -> Vsym.t -> rule 
val t_random_oracle : ocmd_pos -> ctxt -> ctxt -> Vsym.t -> tactic

(** [rexcept p es ju] returns the judgment resulting from replacing
    the sampling [r <- d \ es'] at position [p] in [ju] with the
    sampling [r <- d \ es], i.e., it replaces the (possibly empty)
    set of excepted values [es'] with [es]. *)
val rexcept  : gcmd_pos -> expr list -> rule 
val t_except : gcmd_pos -> expr list -> tactic

(** [rexcept_oracle p es ju] returns the judgment resulting from
    replacing the sampling [r <- d \ es'] at oracle position [p]
    in [ju] with the sampling [r <- d \ es], i.e., it replaces the
    (possibly empty) set of excepted values [es'] with [es]. *)    
val rexcept_oracle  : ocmd_pos -> expr list -> rule 
val t_except_oracle : ocmd_pos -> expr list -> tactic

(** [radd_test p tnew asym vs ju] returns the judgments resulting from
     adding the test [tnew] at oracle position [p = (i,j,k)]. The two new
     judgments for [ju = G : E] are (1) [ G' : E ] where [G'] is obtained
     from [G] by adding the test [tnew] to the oracle
     and (2) [ G'_{1..i}; vs <- A() : t /\ not tnew]
     where [G'_{1..i}] is the prefix of [G'] including [i] and [t] is
     the original test in the oracle. *)
val radd_test  : ocmd_pos -> expr -> Asym.t -> Vsym.t list -> rule 
val t_add_test : ocmd_pos -> expr -> Asym.t -> Vsym.t list -> tactic

(** [rrewrite_oracle p d j] returns the judgment resulting from rewriting
    commands after oracle position [p] with the equality at position [p]
    in direction [d]. *)
val rrewrite_oracle  : ocmd_pos -> direction -> rule 
val t_rewrite_oracle : ocmd_pos -> direction -> tactic

(** [rswap p i ju] returns the judgment resulting from moving the
    command at position [p] [i] positions forward. *)
val rswap  : gcmd_pos -> int -> rule 
val t_swap : gcmd_pos -> int -> tactic

(** [rswap p i ju] returns the judgment resulting from swapping
    the command at oracle positions [p] [i] positons forward. *)
val rswap_oracle  : ocmd_pos -> int -> rule 
val t_swap_oracle : ocmd_pos -> int -> tactic

(** [rrandom_indep ju] completes the proof of judgments of the
     form [(G; r <- d) : E] where [E = /\_i ci] and
     (a) [ci = (r = e)]  where r does not occur in e,
     (b) [ci = (e = r)]  where r does not occur in e, or
     (c) [ci = (r in L)] where r does not occur in L. *)
val rrandom_indep  : rule 
val t_random_indep : tactic

(** [rassm_decision dir vmap assm ju] returns the judgment resulting from
    applying the decisional assumption [assm] with the variable renaming
    [vmap] in direction [dir] to [ju]. *)
val rassm_decision  :
  direction -> Vsym.t Vsym.M.t -> assumption_decision -> rule
val t_assm_decision : 
  direction -> Vsym.t Vsym.M.t -> assumption_decision -> tactic

(** [rbad p vsx ju] returns the judgment resulting from
    applying an up-to bad step with respect to a hash-query
    [let y = h(e)] in position [p]. In the new judgments, the
    hash query is replaced by [y <- d ]. The first judgment
    keeps the event and the second judgment uses the event
    [e in \[ x | x <- Lh\]] with variable [vsx]. *)
val rbad  : int -> Vsym.t -> rule
val t_bad : int -> Vsym.t -> tactic 
