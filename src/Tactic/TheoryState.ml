(*s Goals and mappings from strings to variables/symbols. *)

(*i*)
open Assumption
open Syms
open Gsyms

module Ht = Hashtbl
module T = Type
module G = Game
(*i*)

type theory_proof_state =
  | BeforeProof
  | ActiveProof of CoreRules.proof_state
  | ClosedTheory
    (* FIXME: we should store the proof tree here. Extraction works
       only with a closed theory. *)

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
  | ActiveProof g -> g
  | BeforeProof   -> Util.tacerror "cannot apply tactic: no active proof"
  | ClosedTheory  -> Util.tacerror "cannot apply tactic: theory closed"

(*i
let ts_copy ts =
  { ts_lvars      = Ht.copy ts.ts_lvars;
    ts_gvars      = Ht.copy ts.ts_gvars;
    ts_rodecls    = Ht.copy ts.ts_rodecls;
    ts_odecls     = Ht.copy ts.ts_odecls; 
    ts_adecls     = Ht.copy ts.ts_adecls;
    ts_emdecls    = Ht.copy ts.ts_emdecls;
    ts_assms_dec  = Ht.copy ts.ts_assms_dec;
    ts_assms_comp = Ht.copy ts.ts_assms_comp;
    ts_ps         = ts.ts_ps
  }
i*)

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

(*i
let create_var reuse ps s ty =
  if Ht.mem ps.ts_vars s then (
    if reuse then Some (Ht.find ps.ts_vars s)
    else None
  ) else (
    let v = Vsym.mk s ty in
    Ht.add ps.ts_vars s v;
    Some v
  )
i*)

(*i
let ts_importvars ts ju =
  let ts = ts_resetvars ts in
  let import_var vs =
    Ht.add ts.ts_vars (vs.Vsym.id |> Id.name) vs
  in
  Vsym.S.iter import_var (ju_all_vars ju);
  ts
i*)

