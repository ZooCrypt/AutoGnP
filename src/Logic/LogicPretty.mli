(** Pretty printing for CPA events, judgements, and proofs. *)
open Format

include (module type of LogicTypes)

val pp_ce : formatter -> 'a gcpaEvent -> unit
val pp_ce_tag : formatter -> 'a gcpaEvent -> unit
val pp_cj : formatter -> 'a gcpaJudgement -> unit
val models_ent : string
val pph_cj : formatter -> 'a gcpaJudgement -> unit
val pp_cr : formatter -> 'a gcpaRuleLabel -> unit
val pp_cp : formatter -> 'a gcpaProof -> unit
val pp_cps : formatter -> 'a gcpaProof list -> unit