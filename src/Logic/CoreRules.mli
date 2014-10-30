(*s Derived higher-level tactics. *)

(*i*)
open Nondet
open Game
open Expr
open Assumption
open Util
open Syms
open Gsyms
(*i*)

(* \subsection{Proofs representation} *)

(** Renaming of variables *)
type renaming = vs Vsym.M.t

val id_renaming : renaming

(** Low-level rules (extractable to EasyCrypt). *)
type rule_name = 

  (*c equivalence/small statistical distance: main *)
  | Rconv
  | Rswap of gcmd_pos * int
  | Rrnd  of gcmd_pos * vs * ctxt * ctxt
  | Rexc  of gcmd_pos * expr list

  (*c equivalence/small statistical distance: oracle *)
  | Rrw_orcl   of ocmd_pos * direction
  | Rswap_orcl of ocmd_pos * int 
  | Rrnd_orcl  of ocmd_pos * ctxt * ctxt
  | Rexc_orcl  of ocmd_pos * expr list 

  (*c case distinctions, up-to *)
  | Rcase_ev   of bool * expr
  | Radd_test  of ocmd_pos * expr * ads * vs list 
  | Rbad       of gcmd_pos * vs

  (*c logical rules event *)
  | Rctxt_ev   of gcmd_pos * ctxt 
  | Rremove_ev of int list
  | Rmerge_ev  of int * int
  | Rsplit_ev  of int
  | Rrw_ev     of int * direction

  (*c apply assumption *)
  | Rassm_dec  of direction * renaming  * assm_dec
  | Rassm_comp of expr * renaming * assm_comp

  (*c terminal rules *)
  | Radmit of string
  | Rfalse_ev
  | Rrnd_indep of bool * int

type proof_tree = private {
  pt_children : proof_tree list;
  pt_rule     : rule_name;
  pt_ju       : judgment;
}

val pt_replace_children : proof_tree -> proof_tree list -> proof_tree

type goal = judgment

type rule = goal -> rule_name * goal list

type validation = proof_tree list -> proof_tree

type proof_state = {
  subgoals   : goal list;
  validation : validation
}

type tactic = goal -> proof_state nondet

type 'a rtactic = goal -> ('a * proof_state) nondet

val mk_name : unit -> string

exception NoOpenGoal 

(* \subsection{Basic manipulation tactics}  *)
val get_proof : proof_state -> proof_tree
val move_first_last : proof_state -> proof_state
val apply_on_n : int -> tactic -> proof_state -> proof_state nondet
val apply_all : tactic -> proof_state -> proof_state nondet
val rapply_all : 'a rtactic -> proof_state -> ('a * proof_state) nondet
val apply_first : tactic -> proof_state -> proof_state nondet

val merge_proof_states : proof_state list -> (proof_tree list -> proof_tree) -> proof_state

val t_id : tactic
val t_seq : tactic -> tactic -> tactic
val t_seq_list : tactic -> tactic list -> tactic
val t_bind_ignore : 'a rtactic -> ('a -> tactic) -> tactic
val t_bind : 'a rtactic -> ('a -> 'b rtactic) -> 'b rtactic
val t_cut : tactic -> tactic
(* val t_subgoal : tactic list -> proof_state -> proof_state *)


val t_try : tactic -> tactic
val t_or  : tactic -> tactic -> tactic
val t_fail : ('a, Util.F.formatter, unit, 'b nondet) format4 -> 'c -> 'a
val t_ensure_progress : tactic -> tactic

(* \subsection{Core rules of the logic} *)

val radmit : string -> rule
val t_admit : string -> tactic

(** [rconv b j' j] returns [j'] if [j] and [j'] are equal
    after expanding all lets and rewriting with respect
    to the equational theory. *)
val rconv  : bool -> ?do_rename:bool -> judgment -> rule
val t_conv : bool -> ?do_rename:bool -> judgment -> tactic

(** [rctxt_ev ctx i ju] returns the judgment resulting from
    replacing the [i]-th conjunct in the event of [ju]
    with (a) [ctx(a) = ctx(b)] if it is equal to [a = b]
    and (b) [ ctx(a) in \[ ctx(b) | x in l \] ] if it
    is equal to [ a in \[ b | x in l\]]. *)
val rctxt_ev  : int -> ctxt -> rule 
val t_ctxt_ev : int -> ctxt -> tactic

val rcase_ev  : ?flip:bool -> expr -> rule
val t_case_ev : ?flip:bool -> expr -> tactic

val rremove_ev  : int list -> rule 
val t_remove_ev : int list -> tactic 

val rfalse_ev  : rule 
val t_false_ev : tactic 

val rrw_ev   : int -> direction -> rule
val t_rw_ev  : int -> direction -> tactic

val rsplit_ev   : int -> rule
val t_split_ev  : int -> tactic

val rmerge_ev   : int -> int -> rule
val t_merge_ev  : int -> int -> tactic

(** [rrandom p ctx1 ctx2 ju] returns the judgment resulting
    from replacing the sampling [r <- d] at position [p]
    with [r <- d; let r = ctx1]. The rule checks that [ctx2]
    is the inverse of [ctx1]. *)
val rrnd  : gcmd_pos -> ctxt -> ctxt -> rule
val t_rnd : gcmd_pos -> ctxt -> ctxt -> tactic

(** [rrandom p ctx1 ctx2 v ju] returns the judgment resulting
    from replacing the sampling [r <- d] at oracle position [p]
    with [r <- d; let v = ctx1[r]] and substituting v for r
    in the judgment. The rule checks that [ctx2] is the inverse
    of [ctx1]. *)
val rrnd_oracle  : ocmd_pos -> ctxt -> ctxt -> rule 
val t_rnd_oracle : ocmd_pos -> ctxt -> ctxt -> tactic

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
val radd_test  : ocmd_pos -> expr -> Asym.t -> vs list -> rule 
val t_add_test : ocmd_pos -> expr -> Asym.t -> vs list -> tactic

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

(** [rassm_dec dir vmap assm ju] returns the judgment resulting from
    applying the decisional assumption [assm] with the variable renaming
    [vmap] in direction [dir] to [ju]. *)
val rassm_dec  : direction -> renaming -> assm_dec -> rule
val t_assm_dec : direction -> renaming -> assm_dec -> tactic

val rassm_comp  : assm_comp -> expr -> renaming -> rule
val t_assm_comp : assm_comp -> expr -> renaming -> tactic

(** [rbad p vsx ju] returns the judgment resulting from
    applying an up-to bad step with respect to a hash-query
    [let y = h(e)] in position [p]. In the new judgments, the
    hash query is replaced by [y <- d ]. The first judgment
    keeps the event and the second judgment uses the event
    [e in \[ x | x <- Lh\]] with variable [vsx]. *)
val rbad  : int -> vs -> rule
val t_bad : int -> vs -> tactic 
