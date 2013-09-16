open Expr
open Type
open Util

include LogicTypes

module F = Format

let rec pp_ce fmt ev =
  match ev with
  | Guess     -> F.fprintf fmt "Guess" 
  | Ask(h,e)  -> F.fprintf fmt "Ask(%a, %a)" Hsym.pp h pp_exp e
  | Eq(e1,e2) -> F.fprintf fmt "%a = %a" pp_exp e1 pp_exp e2
  | Conj(evs) -> F.fprintf fmt "(%a)" (pp_list " /\\ " pp_ce) evs

let pp_ce_tag fmt ev =
  F.fprintf fmt (if (ev = Guess) then  "1/2" else "0")

let pp_cj fmt j =
  F.fprintf fmt "|=_{%a}@[ %a :@ %a@]"
    pp_ce_tag j.cj_ev
    pp_exp j.cj_cipher 
    pp_ce j.cj_ev

let models_ent = "&#8871;"

let pph_cj fmt j =
  F.fprintf fmt "<big>%s</big><sub>%a</sub>@[ %a :@ %a@]" models_ent
    pp_ce_tag j.cj_ev
    pp_exp j.cj_cipher 
    pp_ce j.cj_ev

let pp_cr fmt r =
  match r with
  | CpaOpt(r,e)                 -> F.fprintf fmt "Opt(r=%a,e=%a)" Rsym.pp r pp_exp e
  | CpaPerm(r,f)                -> F.fprintf fmt "Perm(r=%a,f=%a)" Rsym.pp r Psym.pp f
  | CpaMerge(r1,r2,r)           -> F.fprintf fmt "Merge(r1=%a,r2=%a,r=%a)" Rsym.pp r1 Rsym.pp r2 Rsym.pp r
  | CpaSplit(r,r1,r2)           -> F.fprintf fmt "Split(r=%a,r1=%a,r2=%a)" Rsym.pp r Rsym.pp r1 Rsym.pp r2
  | CpaConj(i)                  -> F.fprintf fmt "Sub(conj-%i)" i
  | CpaNorm                     -> F.fprintf fmt "Sub(norm)"
  | CpaFail1(h,e,r)             -> F.fprintf fmt "Fail1(H=%a,e=%a,r=%a)" Hsym.pp h pp_exp e Rsym.pp r
  | CpaFail2(h,e,r)             -> F.fprintf fmt "Fail2(H=%a,e=%a,r=%a)" Hsym.pp h pp_exp e Rsym.pp r
  | CpaInd                      -> F.fprintf fmt "Ind"
  | CpaRnd(r,c)                 -> F.fprintf fmt "Rnd(r=%a,C=%a)" Rsym.pp r pp_exp c
  | CpaOw(f,r1,tl,tm,r2s,c1,c2) -> F.fprintf fmt "Ow(f=%a,r1=%a,part_r1=([_]{%a,%a},r2s=(%a),C1=%a,C2=%a)"
                                     Psym.pp f Rsym.pp r1 pp_ty tl pp_ty tm (pp_list "," Rsym.pp) r2s pp_exp c1 pp_exp c2
  | CpaEqs(c,r)                 -> F.fprintf fmt "Eqs(%a,%a)" pp_exp c Rsym.pp r
  | CpaAdmit                    -> F.fprintf fmt "Admit"

let rec pp_cp fmt prf =
  F.fprintf fmt "@[%a@\n----[%a]%a@]"
    pp_cj prf.cp_judgement
    pp_cr prf.cp_rl
    pp_cps prf.cp_prems

and pp_cps fmt prfs =
  match prfs with
  | []        -> F.fprintf fmt ""
  | prf::prfs -> F.fprintf fmt "@\n    %a%a" pp_cp prf pp_cps prfs
