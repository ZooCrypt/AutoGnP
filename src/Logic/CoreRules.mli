(** Core rules of the logic. *)

open Game
open Expr
open Assumption
open Util

exception Invalid_cmd of string

val fail_cmd : string -> 'a

val apply : (judgment -> judgment list) -> judgment list -> judgment list

(** [rconv b j' j] returns [j'] if [j] and [j'] are equal
    after expanding all lets and rewriting with respect
    to the equational theory. *)
val rconv : bool -> judgment -> judgment -> judgment list

val rctxt_ev : ctxt -> int -> judgment -> judgment list

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

val rrandom_indep : judgment -> judgment list

val rassm_decision : direction -> Vsym.t Vsym.M.t -> assumption_decision -> judgment -> judgment list

val rbad : int -> Vsym.t -> judgment -> judgment list
