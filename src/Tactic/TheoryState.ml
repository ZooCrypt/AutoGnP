(*s Goals and mappings from strings to variables/symbols. *)

(*i*)
open Syms
open Gsyms
open Util
open Assumption
open CoreRules
open Nondet
open TheoryTypes

module Ht = Hashtbl
module T = Type
module G = Game
(*i*)

let mk_ts () = {
  ts_lvars      = Ht.create 20;
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
  | ActiveProof (g,_,_,_) -> g
  | BeforeProof           -> tacerror "cannot apply tactic: no active proof"
  | ClosedTheory _        -> tacerror "cannot apply tactic: theory closed"

let get_proof_state_back ts = 
  match ts.ts_ps with
  | ActiveProof (_,_,bg,_)  -> bg
  | BeforeProof             -> tacerror "cannot apply tactic: no active proof"
  | ClosedTheory _          -> tacerror "cannot apply tactic: theory closed"

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
