(** Core rules of the logic. *)

open Game
open Expr
open Assumption
open Util

(** Exception that captures rule application errors. *)
exception Invalid_rule of string

(** [fail_rule s] raises a rule application error with information [s]. *)
val fail_rule : string -> 'a

(** [apply ru jus] applies the rule [ru] to the first judgment in [jus]. *)
val apply : (judgment -> judgment list) -> judgment list -> judgment list

(** [rconv b j' j] returns [j'] if [j] and [j'] are equal
    after expanding all lets and rewriting with respect
    to the equational theory. *)
val rconv : bool -> judgment -> judgment -> judgment list

(** [rctxt_ev ctx i ju] returns the judgment resulting from
    replacing the [i]-th conjunct in the event of [ju]
    with (a) [ctx(a) = ctx(b)] if it is equal to [a = b]
    and (b) [ ctx(a) in \[ ctx(b) | x in l \] ] if it
    is equal to [ a in \[ b | x in l\]]. *)
val rctxt_ev : ctxt -> int -> judgment -> judgment list

val remove_ev : int list -> judgment -> judgment list
val merge_ev  : int -> int -> judgment -> judgment list

(** [rrandom p ctx1 ctx2 v ju] returns the judgment resulting
    from replacing the sampling [r <- d] at position [p]
    with [r <- d; let v = ctx1[r]] and substituting v for r
    in the judgment. The rule checks that [ctx2] is the inverse
    of [ctx1]. *)
val rrandom : gcmd_pos -> ctxt -> ctxt -> Vsym.t -> judgment -> judgment list

(** [rrandom p ctx1 ctx2 v ju] returns the judgment resulting
    from replacing the sampling [r <- d] at oracle position [p]
    with [r <- d; let v = ctx1[r]] and substituting v for r
    in the judgment. The rule checks that [ctx2] is the inverse
    of [ctx1]. *)
val rrandom_oracle : ocmd_pos -> ctxt -> ctxt -> Vsym.t -> judgment -> judgment list

(** [rexcept p es ju] returns the judgment resulting from replacing
    the sampling [r <- d \ es'] at position [p] in [ju] with the
    sampling [r <- d \ es], i.e., it replaces the (possibly empty)
    set of excepted values [es'] with [es]. *)
val rexcept : gcmd_pos -> expr list -> judgment -> judgment list

(** [rexcept_oracle p es ju] returns the judgment resulting from
    replacing the sampling [r <- d \ es'] at oracle position [p]
    in [ju] with the sampling [r <- d \ es], i.e., it replaces the
    (possibly empty) set of excepted values [es'] with [es]. *)    
val rexcept_oracle : ocmd_pos -> expr list -> judgment -> judgment list

(** [radd_test p tnew asym vs ju] returns the judgments resulting from
     adding the test [tnew] at oracle position [p = (i,j,k)]. The two new
     judgments for [ju = G : E] are (1) [ G' : E ] where [G'] is obtained
     from [G] by adding the test [tnew] to the oracle
     and (2) [ G'_{1..i}; vs <- A() : t /\ not tnew]
     where [G'_{1..i}] is the prefix of [G'] including [i] and [t] is
     the original test in the oracle. *)
val radd_test : ocmd_pos -> expr -> Asym.t -> Vsym.t list -> judgment -> judgment list

(** [rrewrite_oracle p d j] returns the judgment resulting from rewriting
    commands after oracle position [p] with the equality at position [p]
    in direction [d]. *)
val rrewrite_oracle : ocmd_pos -> direction -> judgment -> judgment list

(** [rswap p i ju] returns the judgment resulting from moving the
    command at position [p] [i] positions forward. *)
val rswap : gcmd_pos -> int -> judgment -> judgment list

(** [rswap p i ju] returns the judgment resulting from swapping
    the command at oracle positions [p] [i] positons forward. *)
val rswap_oracle : ocmd_pos -> int -> judgment -> judgment list

(** [rrandom_indep ju] completes the proof of judgments of the
     form [(G; r <- d) : E] where [E = /\_i ci] and
     (a) [ci = (r = e)]  where r does not occur in e,
     (b) [ci = (e = r)]  where r does not occur in e, or
     (c) [ci = (r in L)] where r does not occur in L. *)
val rrandom_indep : judgment -> judgment list

(** [rassm_decision dir vmap assm ju] returns the judgment resulting from
    applying the decisional assumption [assm] with the variable renaming
    [vmap] in direction [dir] to [ju]. *)
val rassm_decision : direction -> Vsym.t Vsym.M.t -> assumption_decision -> judgment -> judgment list

(** [rbad p vsx ju] returns the judgment resulting from
    applying an up-to bad step with respect to a hash-query
    [let y = h(e)] in position [p]. In the new judgments, the
    hash query is replaced by [y <- d ]. The first judgment
    keeps the event and the second judgment uses the event
    [e in \[ x | x <- Lh\]] with variable [vsx]. *)
val rbad : int -> Vsym.t -> judgment -> judgment list
