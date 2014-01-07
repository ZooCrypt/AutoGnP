(** Core rules of the logic. *)

open Game
open Expr
open Assumption

exception Invalid_cmd of string

val fail_cmd : string -> 'a

val apply : (judgment -> judgment list) -> judgment list -> judgment list

val delay : 'a list -> 'a list

val fail_if_occur : Vsym.t -> judgment -> string -> unit

val check_conv : judgment -> judgment -> bool

val rconv : bool -> judgment -> judgment -> judgment list

val rctxt_ev : ctxt -> int -> judgment -> judgment list

val ensure_bijection : ctxt -> ctxt -> expr -> unit

val rrandom : int -> ctxt -> ctxt -> Vsym.t -> judgment -> judgment list

val rrandom_oracle :
  int * int * int ->
  ctxt -> ctxt -> Vsym.t -> judgment -> judgment list

val rexcept : int -> expr list -> judgment -> judgment list

val rexcept_oracle : int * int * int -> expr list -> judgment -> judgment list

val radd_test :
  int * int * int ->
  expr -> Asym.t -> Vsym.t list -> judgment -> judgment list

val rrewrite_oracle : int * int * int -> Util.direction -> judgment -> judgment list

(* val disjoint : Se.t -> Se.t -> bool *)

(* val check_swap : ('a list -> Se.t) -> ('a list -> Se.t) -> 'a -> 'a list -> unit *)

val swap : int -> int -> judgment -> judgment

val rswap : int -> int -> judgment -> judgment list

val swap_oracle : int * int * int -> int -> judgment -> judgment

val rswap_oracle : int * int * int -> int -> judgment -> judgment list

val check_event : Vsym.t -> IdType.internal gexpr -> bool

val rrandom_indep : judgment -> 'a list

val rassm_decision :
  Util.direction ->
  Vsym.t Vsym.M.t ->
  assumption_decision -> judgment -> judgment list

val rbad : int -> Vsym.t -> judgment -> judgment list
