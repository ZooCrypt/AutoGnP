(*i*)
open Util
open Nondet
open Syms
open Gsyms
open Type
open Assumption
open CoreRules
(*i*)

(** There are three possible positions in a theory:
   \begin{itemize}
   \item Before the proof: There is no proof state.
   \item Inside the proof:
    A state
    [ActiveProof(cps,lpss,rpss,ops)]
    contains the current proof state [cps], alternative proof states
    [lpss] to the left and [rpss] right, and the previous proof state [ops]
    (if it exists).
    The alternative proof states are used for backtracking if rules
    return more than one alternative and the previous proof state is used to
    compute (and print) the changes performed by proof steps.
   \item After the proof: The theory is closed and there is a proof tree.
   \end{itemize} *)
type theory_proof_state =
  | BeforeProof
  | ActiveProof
    of proof_state * proof_state list * proof_state nondet * proof_state option
  | ClosedTheory of proof_tree

(** We implicitly define length and group variables for which
    sharing is required when the same string occurs in
    different states. *)
type theory_state = {

  (* implicitly defined and shared *)
  ts_lvars      : (string,Lenvar.id)   Hashtbl.t;
  ts_gvars      : (string,Groupvar.id) Hashtbl.t;

  (* explicitly defined *)
  ts_rodecls    : Hsym.t      Mstring.t;
  ts_odecls     : Osym.t      Mstring.t;
  ts_adecls     : Asym.t      Mstring.t;
  ts_emdecls    : Esym.t      Mstring.t;
  ts_assms_dec  : assm_dec    Mstring.t;
  ts_assms_comp : assm_comp   Mstring.t;

  ts_ps         : theory_proof_state;

  (*c FIXME: Add some state to increase sharing during
      proof search. We want rules to commute. *)

}
