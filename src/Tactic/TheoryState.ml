(*s Goals and mappings from strings to variables/symbols. *)

(*i*)
open Syms
open Gsyms
open Util
open Assumption
open CoreRules
open Nondet

module Ht = Hashtbl
module T = Type
module G = Game
(*i*)

type theory_proof_state =
  | BeforeProof
  | ActiveProof  of (proof_state * proof_state nondet) 
  | ClosedTheory of proof_tree

type theory_state =
  { (* theory definitions:
       we might have to make these local to a goal to support, e.g. ,reduction steps. *)
    ts_lvars      : (string, T.Lenvar.id) Ht.t;    (*r length vars used in theory *)
    ts_gvars      : (string, T.Groupvar.id) Ht.t;  (*r group vars used in theory *)
    ts_rodecls    : (string, Hsym.t) Ht.t;         (*r declared hash functions *)
    ts_odecls     : (string, Osym.t) Ht.t;         (*r declared oracles *)
    ts_adecls     : (string, Asym.t) Ht.t;         (*r declared adversaries *)
    ts_emdecls    : (string, Esym.t) Ht.t;         (*r declared adversaries *)
    ts_assms_dec  : (string, assm_dec) Ht.t;       (*r defined decisional assumptions *)
    ts_assms_comp : (string, assm_comp) Ht.t;      (*r defined computational assumptions *)
    ts_ps         : theory_proof_state             (*r proof state *)
  }

let mk_ts () =
  { ts_lvars      = Ht.create 20;
    ts_gvars      = Ht.create 20;
    ts_rodecls    = Ht.create 20;
    ts_odecls     = Ht.create 20; 
    ts_adecls     = Ht.create 20;
    ts_emdecls    = Ht.create 20;
    ts_assms_dec  = Ht.create 5;
    ts_assms_comp = Ht.create 5;
    ts_ps         = BeforeProof
  }

let get_proof_state ts = 
  match ts.ts_ps with
  | ActiveProof (g,_)  -> g
  | BeforeProof        -> tacerror "cannot apply tactic: no active proof"
  | ClosedTheory _     -> tacerror "cannot apply tactic: theory closed"

let get_proof_state_back ts = 
  match ts.ts_ps with
  | ActiveProof (_,bg)  -> bg
  | BeforeProof         -> tacerror "cannot apply tactic: no active proof"
  | ClosedTheory _      -> tacerror "cannot apply tactic: theory closed"


let get_proof_tree ts = 
  match ts.ts_ps with
  | ActiveProof _   -> tacerror "cannot obtain proof tree, finish proof with qed "
  | BeforeProof     -> tacerror "cannot obtain proof, no proof started yet"
  | ClosedTheory pt -> pt

let create_lenvar ps s =
  try Ht.find ps.ts_lvars s 
  with Not_found ->
    let lv = T.Lenvar.mk s in
    Ht.add ps.ts_lvars s lv;
    lv

let create_groupvar ps s =
  try Ht.find ps.ts_gvars s 
  with Not_found ->
    let gv = T.Groupvar.mk s in
    Ht.add ps.ts_gvars s gv;
    gv
