(*i*)
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
