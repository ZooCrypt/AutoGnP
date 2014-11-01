(*s Decisional and computational assumptions. *)

(*i*)
open Util
open Syms
open Expr
open Game
open Gsyms
(*i*)

(** Decisional assumptions. *)
type assm_dec = {
  ad_name       : string;       (*r name of assumption *)
  ad_prefix1    : gdef;         (*r prefix for left *)
  ad_prefix2    : gdef;         (*r prefix for right *)
  ad_acalls     : (Asym.t * Vsym.t list * (expr * expr)) list;
                                (*r adversary calls (same asym) and
                                    arguments/returned variables on left and right *)
  ad_symvars    : vs list list; (*r symmetric in given variables *)
}

val pp_assm_dec :  Util.F.formatter -> assm_dec -> unit

val mk_assm_dec : string -> gdef -> gdef -> (Vsym.t list) list -> assm_dec

val needed_vars : direction  -> assm_dec -> Vsym.t list

val private_vars : assm_dec -> Se.t

val ad_inst : Vsym.t Vsym.M.t -> assm_dec -> assm_dec

(** Computational assumptions. *)
type assm_comp = private {
  ac_name       : string;       (*r name of assumption *)
  ac_prefix     : gdef;         (*r prefix of assumption *)
  ac_event_var  : Vsym.t;       (*r variable in event *)
  ac_event      : Expr.expr;    (*r event expression *)
  ac_pubvars    : Vsym.S.t;     (*r public variables *)
  ac_privvars   : Vsym.S.t;     (*r private variables *)
  ac_symvars    : vs list list; (*r symmetric in given variables *)
}

val mk_assm_comp :
  string -> gdef -> Vsym.t -> expr -> Vsym.S.t -> vs list list -> assm_comp

val ac_inst : Vsym.t Vsym.M.t -> assm_comp -> assm_comp
