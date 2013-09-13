
(** Types for CPA logic: Events, judgements, and proofs. *)

(* This .ml file exists only because ocsigen does not seem to handle modules
   for which there is only an mli file. *)

open Expr
open IdType
open Type

(** CPA events. *)
type 'a gcpaEvent =
    Guess
  | Ask  of 'a Hsym.gt * 'a gexpr
  | Eq   of 'a gexpr * 'a gexpr
  | Conj of 'a gcpaEvent list

type cpaEvent = internal gcpaEvent

type ecpaEvent = exported gcpaEvent


type 'a gcpaJudgement = {cj_cipher : 'a gexpr; cj_ev : 'a gcpaEvent}

type cpaJudgement = internal gcpaJudgement

type ecpaJudgement = exported gcpaJudgement

(** A context (to deduce a term) is an expr that might contain
    the variable [Star]. *)
type 'a gcontext = 'a gexpr

type context = internal gcontext

type econtext = exported gcontext

type 'a gcpaRuleLabel = 
    CpaOpt   of 'a Rsym.gt * 'a gexpr
    (** [Opt(r,e)]: Replace r by r + e in judgement *)
  | CpaPerm  of 'a Rsym.gt * 'a Psym.gt
    (** [Perm(r,f)]: Replace r by f(r) in judgement *)
  | CpaMerge of 'a Rsym.gt * 'a Rsym.gt * 'a Rsym.gt
    (** [Merge(r1,r2,r)]: Replace r1||r2 by r in judgement *)
  | CpaSplit of 'a Rsym.gt * 'a Rsym.gt * 'a Rsym.gt
    (** [Split(r,r1,r1)]: Replace r by r1||r2 in judgement *)
  | CpaConj of int
    (** [Conj(i)] choose i-th conjunct in judgement *)
  | CpaNorm
    (** [EqE] Compute normal form of judgement *)
  | CpaFail1 of 'a Hsym.gt * 'a gexpr * 'a Rsym.gt
    (** [Fail1(H,e,r)]: replace H(e) by r in judgement *)
  | CpaFail2 of 'a Hsym.gt * 'a gexpr * 'a Rsym.gt
    (** [Fail2(H,e,r)]: replace H(e) by r in judgement *)
  | CpaInd 
    (** [Ind]: no Msg in J *)
  | CpaRnd of  'a Rsym.gt * 'a gcontext
    (** [Rnd(C,r)]: Use C to deduce r from queried expression *)
  | CpaOw of 'a Psym.gt *
             'a Rsym.gt * 'a gty * 'a gty *
             'a Rsym.gt list *
             'a gcontext *
             'a gcontext
    (** [Ow(f,r1,k,l,r2s,C1,C2)]: Given r2 and known expression, deduce c* via C2, then
        deduce (partial [_]_k^l) input r1 of f using C1 *)
  | CpaEqs of 'a gcontext * 'a Rsym.gt
    (** [Eqs(C,r)J]: ... FIXME *)
  | CpaAdmit

type cpaRuleLabel = internal gcpaRuleLabel

type ecpaRuleLabel = exported gcpaRuleLabel

(** A CPA proof is a tree where each node is labeled with a {! gcpaRuleLabel}
    and a {! gcpaJudgement}. *)
type 'a gcpaProof =
  { cp_rl : 'a gcpaRuleLabel;
    cp_judgement : 'a gcpaJudgement;
    cp_prems : ('a gcpaProof) list
  }

(** Internal CPA proof *)
type cpaProof = internal gcpaProof

(** Exported CPA proof *)
type ecpaProof = exported gcpaProof
