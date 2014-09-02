(*s Goals and mappings from strings to variables/symbols. *)

(*i*)
open Type
open Assumption
open Syms
open Gsyms
(*i*)

(** There are three possible positions in a theory:
   Before the proof.
   Inside the proof.
   After the proof, the theory is closed (the proof is completed). *)
type theory_proof_state =
    BeforeProof
  | ActiveProof of CoreRules.proof_state
  | ClosedTheory

type theory_state = {
  ts_lvars      : (string, Lenvar.id)   Hashtbl.t;
  ts_gvars      : (string, Groupvar.id) Hashtbl.t;
  ts_rodecls    : (string, Hsym.t)      Hashtbl.t;
  ts_odecls     : (string, Osym.t)      Hashtbl.t;
  ts_adecls     : (string, Asym.t)      Hashtbl.t;
  ts_emdecls    : (string, Esym.t)      Hashtbl.t;
  ts_assms_dec  : (string, assm_dec)    Hashtbl.t;
  ts_assms_comp : (string, assm_comp)   Hashtbl.t;
  ts_ps         : theory_proof_state;
}

val mk_ts : unit -> theory_state

val get_proof_state : theory_state -> CoreRules.proof_state

val create_lenvar : theory_state -> string -> Lenvar.id

val create_groupvar : theory_state -> string -> Groupvar.id
