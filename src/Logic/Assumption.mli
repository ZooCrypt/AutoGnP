(*s Decisional and computational assumptions. *)

(*i*)
open Util
open Syms
open Expr
open Game
open Gsyms
(*i*)

(** Decisional assumptions. *)
type assm_dec = private {
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

val needed_vars_dec : direction  -> assm_dec -> Vsym.t list

val private_vars_dec : assm_dec -> Se.t

val inst_dec : Vsym.t Vsym.M.t -> assm_dec -> assm_dec

(** Computational assumptions. *)
type assm_comp = private {
  ac_name       : string;       (*r name of assumption *)
  ac_prefix     : gdef;         (*r prefix of assumption *)
  ac_event      : Expr.expr;    (*r event expression *)
  ac_acalls     : (Asym.t * Vsym.t list * expr) list;
   (*r adversary calls (same asym) and arguments/returned variables *)
  ac_symvars    : vs list list; (*r symmetric in given variables *)
}

val pp_assm_comp :  Util.F.formatter -> assm_comp -> unit

val mk_assm_comp : string -> gdef -> expr -> vs list list -> assm_comp

val private_vars_comp : assm_comp -> Se.t

val inst_comp : Vsym.t Vsym.M.t -> assm_comp -> assm_comp
