(** High-level proof construction for CPA. *)
open ParserUtil
open Logic
open LogicParse

(** {1 Proof state and proving} *)

(** State of proof. *)

type proofState = {
  ps_history : string list;  (** history of commands *)
  ps_proof   : cpaProof;     (** proof (tree) *)
}

(** Apply given command(s) to proofstate. *)
val apply : string -> proofState -> proofState

(* * Norm expression given by string with respect to typing environment
    implicitly defined by path of proofstate. *)
(* val norm_for_path : path -> proofState -> string -> Expr.expr *)

(* * Apply context to term (both given as strings) with respect to
    typing environment implicitly defined by path of proofstate. *)
(* val apply_ctxt_for_path : path -> proofState -> string -> string -> Expr.expr *)

(** {2 Textual proof state for storage} *)

(** Textual representation of scheme. *)
type tscheme = {
  ts_msg_decl   : string;
  ts_hash_decls : string;
  ts_perm_decls : string;
  ts_rvar_decls : string;
  ts_cipher     : string;
}

(** Textual representation of proof state. *)
type tproofState = {
  tps_scheme : tscheme;
  tps_history : string list;
}

(** Parse textual representation of proof state. *)
val ps_of_tps : tproofState -> proofState