(** Information about applicable rules. *)

open Cpa

(** Information about applicable rules *)
type applicableInfo = {
  ai_ind              : bool;
  ai_msg_occ          : bool;
  ai_nf               : bool;
  ai_conjs            : int list;
  ai_rvars            : Rsym.t list;
  ai_rvars_xor        : (Rsym.t * Expr.expr) list;
  ai_rvars_non_basic  : Rsym.t list;
  ai_hashes           : Hsym.t list;
  ai_rvars_event_only : Rsym.t list;
  ai_perms_rvars      : (Psym.t * Rsym.t * Rsym.t list) list;
  ai_queried_msgs     : Expr.expr list;
}

(** Compute applicableInfo for given judgement *)
val compute_ai : cpaJudgement -> applicableInfo
