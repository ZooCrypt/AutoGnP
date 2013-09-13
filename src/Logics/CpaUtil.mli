(** Generic functions for CPA events, judgements, and proofs. *)

open Expr
(* open CpaTypes *)
open Type
open Id

include (module type of CpaPretty)

(** {1 map and iter } *)

(** [map_expr_ce g ce] maps [g] over all expressions in [ce]. *)
val map_expr_ce : ('a gexpr -> 'a gexpr) -> 'a gcpaEvent -> 'a gcpaEvent

(** [map_expr_cj g cj] maps [g] over all expressions in [cj]. *)
val map_expr_cj : ('a gexpr -> 'a gexpr) -> 'a gcpaJudgement -> 'a gcpaJudgement

(** [map_expr_rl g rl] maps [g] over all expressions in [rl]. *)
val map_expr_rl : ('a gexpr -> 'a gexpr) -> 'a gcpaRuleLabel -> 'a gcpaRuleLabel

(** [map_expr_cp g cp] maps [g] over all expressions in [cp]. *)
val map_expr_cp : ('a gexpr -> 'a gexpr) -> 'a gcpaProof -> 'a gcpaProof

(** [iter_expr_ce g ce] iterates [g] over all expressions in [ce]. *)
val iter_expr_ce : ('a gexpr -> unit) -> 'a gcpaEvent -> unit

(** [iter_expr_cj g cj] iterates [g] over all expressions in [cj]. *)
val iter_expr_cj : ('a gexpr -> unit) -> 'a gcpaJudgement -> unit

(** [iter_expr_rl g rl] iterates [g] over all expressions in [rl]. *)
val iter_expr_rl : ('a gexpr -> unit) -> 'a gcpaRuleLabel -> unit

(** [iter_expr_cp g cp] iterates [g] over all expressions in [cp]. *)
val iter_expr_cp : ('a gexpr -> unit) -> 'a gcpaProof -> unit

(** [find_expr_ce p ce] searches for the first expression in [ce]
    satisfying [p]. *)
val find_expr_ce : ('a gexpr -> bool) -> 'a gcpaEvent -> 'a gexpr option

(** [find_expr_cj p cj] searches for the first expression in [cj]
    satisfying [p]. *)
val find_expr_cj : ('a gexpr -> bool) -> 'a gcpaJudgement -> 'a gexpr option

type ident = ITyvar of Tyvar.id | IIdent of id

module Si : Set.S with type elt=ident
val si_unions : Si.t list -> Si.t
val list_of_si : Si.t -> ident list

module Mstring : Map.S with type key = string

module Mnt : Map.S with type key = (string * int)

(** {2 Extract identifiers.  } *)

(** [idents_ty ty] returns all identifiers in [ty]. *)
val idents_ty : ty -> Si.t

(** [idents_rsym rs] returns all identifiers in [rs]. *)
val idents_rsym : Rsym.t -> Si.t

(** [idents_psym ps] returns all identifiers in [ps]. *)
val idents_psym : Psym.t -> Si.t

(** [idents_hsym hs] returns all identifiers in [hs]. *)
val idents_hsym : Hsym.t -> Si.t

(** [idents_e e] returns all identifiers in [e]. *)
val idents_e : expr -> Si.t

(** [idents_ce ce] returns all identifiers in [ce]. *)
val idents_ce : cpaEvent -> Si.t

(** [idents_cj cj] returns all identifiers in [cj]. *)
val idents_cj : cpaJudgement -> Si.t

(** [idents_rl rl] returns all identifiers in [rl]. *)
val idents_rl : cpaRuleLabel -> Si.t

(** [idents_cp cp] returns all identifiers in [cp]. *)
val idents_cp : cpaProof -> Si.t

(** {3 Export } *)

val export_ce : cpaEvent -> ecpaEvent
val export_cj : cpaJudgement -> ecpaJudgement
val export_rl : cpaRuleLabel -> ecpaRuleLabel
val export_cp : cpaProof -> ecpaProof

(** {4 rename } *)

(** [rename_cp cp] exports [cp] and renames the [int]s
    in the identifiers such that they are minimal, but still
    unique together with the strings. If names are already
    unique on their own, this means all tags will be 0. *)
val rename_cp : cpaProof -> ecpaProof

(** Rename expression as described for {! rename_cp}. *)
val rename_e : expr -> eexpr

(** rename type as described for {! rename_cp}. *)
val rename_ty : ty -> ety

(** {5 pretty printing } *)

val pp_e : Format.formatter -> expr -> unit
val typeError_to_string_rn : ty * ty * expr * expr option * 'a -> string
