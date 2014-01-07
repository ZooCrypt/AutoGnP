(** Core rules of the logic. *)

open Game
open Expr
open Assumption
open Util

exception Invalid_cmd of string

val fail_cmd : string -> 'a

val apply : (judgment -> judgment list) -> judgment list -> judgment list

val rconv : bool -> judgment -> judgment -> judgment list

val rctxt_ev : ctxt -> int -> judgment -> judgment list

val rrandom : int -> ctxt -> ctxt -> Vsym.t -> judgment -> judgment list

val rrandom_oracle : ocmd_pos -> ctxt -> ctxt -> Vsym.t -> judgment -> judgment list

val rexcept : int -> expr list -> judgment -> judgment list

val rexcept_oracle : ocmd_pos -> expr list -> judgment -> judgment list

val radd_test : ocmd_pos -> expr -> Asym.t -> Vsym.t list -> judgment -> judgment list

val rrewrite_oracle : ocmd_pos -> direction -> judgment -> judgment list

val rswap : int -> int -> judgment -> judgment list

val rswap_oracle : ocmd_pos -> int -> judgment -> judgment list

val rrandom_indep : judgment -> 'a list

val rassm_decision : direction -> Vsym.t Vsym.M.t -> assumption_decision -> judgment -> judgment list

val rbad : int -> Vsym.t -> judgment -> judgment list
