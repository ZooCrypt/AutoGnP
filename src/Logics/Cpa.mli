(** CPA rules and rule application. *)

open Expr

include (module type of CpaUtil)

(** {1 Helper functions for judgements and proofs} *)

(** Constructor function for CPA proof. *)
val mk_cp : 'a gcpaRuleLabel -> 'a gcpaJudgement -> 'a gcpaProof list -> 'a gcpaProof

(** Find message in CPA judgement. Returns [None] if there is no
    message. *)
val find_msg : cpaJudgement -> expr option

(** Return set of random variables in CPA event *)
val rvars_ce : IdType.internal gcpaEvent -> Se.t

(** Return set of random variables in CPA judgement. *)
val rvars_cj : cpaJudgement -> Se.t

(** Return set of random variables in CPA proof. *)
val rvars_cp : cpaProof -> Se.t

(** Return list of [Ask]ed messages in CPA event. *)
val askEventMessages : 'a gcpaEvent -> 'a gexpr list

(** {2 Rules of CPA logic} *)

(** Application failure for given judgement. *)
exception AppFailure of cpaJudgement * string

(** Compute normal form of given judgement with respect to
    equational theory. *)
val appNorm : cpaJudgement -> cpaProof

(** [appConj i j] removes the [i]th event from the judgement. *)
val appConj : int -> cpaJudgement -> cpaProof

(** [appOpt rs e j] replaces the random variable [rs] with
    [rs + e] in [j]. *)
val appOpt : Rsym.t -> expr -> cpaJudgement -> cpaProof

(** [appPerm rs f j] replaces the random variable [rs] with
    [f^-1(rs)] in [j]. *)
val appPerm : Rsym.t -> Psym.t -> cpaJudgement -> cpaProof

(** [appSplit r r1 r2] splits [r] into [r1 || r2]. *)
val appSplit : Rsym.t -> Rsym.t -> Rsym.t -> cpaJudgement -> cpaProof

(** [appMerge r1 r2 r] merges [r1] and [r2] into [r]. *)
val appMerge : Rsym.t -> Rsym.t -> Rsym.t -> cpaJudgement -> cpaProof

(** [appFail1 h r j] applies the [fail1] rule for [h] to [j]
     using [r] as a fresh random variable. *)
val appFail1 : Hsym.t -> Rsym.t -> cpaJudgement -> cpaProof

(** [appFail2 h r j] applies the [fail2] rule for [h] to [j]
     using [r] as a fresh random variable. *)
val appFail2 : Hsym.t -> Rsym.t -> cpaJudgement -> cpaProof

(** [appInd j] solves the judgement if the message does not occur
    in the cipher and the event is [Guess]. *)
val appInd : cpaJudgement -> cpaProof

(** [appRnd r c j] applies the [Rnd] rule to judgement [j]
    for the random variable [r] which can be deduced using
    context [c]. *)
val appRnd : Rsym.t -> context -> cpaJudgement -> cpaProof

(** [appOw p r ty1 ty2 rs c1 c2 j] applies the [OW] rule
    where the projection of [ty2] bits starting at [ty1]
    from [r], the input of [p] can be deduced using [c2].
    Additionally, with the random variables [rs], [c2] can
    be used to deduce the ciphertext. *)
val appOw : Psym.t -> Rsym.t -> Type.ty -> Type.ty -> Rsym.t list ->
            context -> context -> cpaJudgement -> cpaProof

(** [appAdmit j] solves the judgement using the [Admit] rule. *)
val appAdmit : 'a gcpaJudgement -> 'a gcpaProof

(** {3 Rule application} *)

(** Zero-indexed path in proof (tree). *)
type path = int list

(** Exception raised if one of following functions is given invalid path. *)
exception InvalidPath of cpaProof * path * string

(** Exception raised if one of following functions is given admit index. *)
exception InvalidAdmit of cpaProof * int * string

(** [applyAt path g pr] applies [g] to CPA judgement at [path] in [pr]
    and replaces the corresponding node in the proof. *)
val applyAt : path -> (cpaJudgement -> cpaProof) -> cpaProof -> cpaProof

(** [cpAt path pr] returns the subproof of [pr] at [path]. *)
val cpAt : path -> cpaProof -> cpaProof

(** [admitPaths pr] returns the list of paths to [Admit] nodes
    in [pr]. *)
val admitPaths : 'a gcpaProof -> int list list

(** [cjAt path pr] returns the judgement in [pr] at [path]. *)
val cjAt : path -> cpaProof -> cpaJudgement
