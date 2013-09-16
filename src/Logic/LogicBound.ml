open Type
open Logic
open Expr

(* ----------------------------------------------------------------------- *)
(** {1 Probability and time bounds: representation and computation} *)

(** Represents factor defined in terms of the number of queries
    to various oracles. *)
type qs =
    QOne
  | QTimes of qs * qs
  | QHash  of Hsym.et
  | QDec

(** Represents time complexity of algorithm. *)
type time =
    TAdv
  | TOne
  | TTimes of qs * time
  | TPerm of Psym.et
  | TPlus of time * time

(** Represents success probability *)
type prob =
    PZero
  | PHalf
  | PTimes      of qs * prob
  | PPlus       of prob * prob
  | PTwoPowMinus of ety
  | PSuccOwSpd   of Psym.et * ety * ety * qs * time
  | PSuccOw      of Psym.et * time
  | PUndefined   of string

type params =
  { p_qD: qs;
    p_mqH: (Hsym.t * qs) list; (* no entry if q_H = qH *)
    p_ti: time
  }

let params_def =
  { p_qD = QDec; p_mqH = []; p_ti = TAdv }

let rec hashlist_of_ev ev = match ev with
  | Ask(h,_) -> [h]
  | Conj [ev] -> hashlist_of_ev ev
  | Conj(ev::evs) -> hashlist_of_ev ev @ hashlist_of_ev (Conj evs)
  | _ -> failwith "bound_of_proof: invalid event"

let rec qs_of_hashlist hl = match hl with
  | []    -> QOne
  | [h]   -> QHash h
  | h::hs -> QTimes(QHash h, qs_of_hashlist hs)

let time_of_context ctx =
  let rec go t c =
    let t' = e_sub_fold go t c in
    match c.e_node with
    | P(f,_) | Pinv(f,_) ->
        (match t' with
         | TOne -> TPerm f
         | _    -> TPlus(TPerm f,t'))
    | _ -> t'
  in go TOne ctx

let bound_of_proof keep_spd cp0 =
   let admits = ref 0 in
    (* FIXME: check if the part corresponding to hash query is actually used by
              context C2 *)
   let bound_ow cp f k l c1 c2 p =
      if not keep_spd && is_ty_zero k && f.Psym.dom = l then (
        let set_size = qs_of_hashlist (hashlist_of_ev cp.cp_judgement.cj_ev) in
        let ti = TPlus (p.p_ti, (TPlus(time_of_context c2,
                                       TTimes(set_size, TPlus(TPerm f, time_of_context c1))))) in
        PSuccOw(f,ti)
      ) else (
        let set_size = qs_of_hashlist (hashlist_of_ev cp.cp_judgement.cj_ev) in
        let ti = TPlus (p.p_ti, (TPlus(time_of_context c2,
                                     TTimes(set_size, time_of_context c1)))) in
        PSuccOwSpd(f,k,l,set_size,ti)
      )
   in
   let bound_rnd cp r _p =
     let guess_tries = qs_of_hashlist (hashlist_of_ev cp.cp_judgement.cj_ev) in
     PTimes(guess_tries,(PTwoPowMinus r.Rsym.ty))
   in
   let rec go cp p =
     match cp.cp_rl, cp.cp_prems with
     | CpaOpt   _, [ cp1 ]
     | CpaPerm  _, [ cp1 ]
     | CpaSplit _, [ cp1 ]
     | CpaMerge _, [ cp1 ]
     | CpaConj _,  [ cp1 ]
     | CpaNorm,    [ cp1 ] -> go cp1 p
     | CpaFail1 _, [ cp1; cp2 ]
     | CpaFail2 _, [ cp1; cp2 ] -> let b1 = go cp1 p in
                                   let b2 = go cp2 p in
                                   PPlus(b1, b2)
     | CpaInd, []  -> PHalf
     | CpaRnd(r,_c), [] -> bound_rnd cp r p
     | CpaOw(f,_rv,k,l,_rs,c1,c2), [] -> bound_ow cp f k l c1 c2 p
     | CpaAdmit, [] -> let adm = !admits in
                       incr admits;
                       PUndefined (Format.sprintf "%i" adm)
     | CpaEqs _, [] -> failwith "FIXME: CpaEqs case not implemented yet"
     | _, _         -> failwith "CpaBound.bound_of_proof: invalid proof"
   in go cp0 params_def

(* ----------------------------------------------------------------------- *)
(** {2 Pretty printing} *)

let rec pp_qs fmt qs =
  match qs with
  | QOne            -> Format.fprintf fmt "1"
  | QTimes(qs1,qs2) -> Format.fprintf fmt "%a * %a" pp_qs qs1 pp_qs qs2
  | QDec            -> Format.fprintf fmt "qD"
  | QHash h         -> Format.fprintf fmt "q_%a" Hsym.pp h

let rec pp_time fmt t =
  match t with
  | TAdv            -> Format.fprintf fmt "tA"
  | TOne            -> Format.fprintf fmt "1"
  | TTimes(qs,TOne) -> Format.fprintf fmt "%a" pp_qs qs
  | TTimes(qs,t)    -> Format.fprintf fmt "%a * %a" pp_qs qs pp_time t
  | TPerm(f)        -> Format.fprintf fmt "t_%a" Psym.pp f
  | TPlus(TOne,t2)  -> Format.fprintf fmt "%a" pp_time t2
  | TPlus(t1,TOne)  -> Format.fprintf fmt "%a" pp_time t1
  | TPlus(t1,t2)    -> Format.fprintf fmt "%a + %a" pp_time t1 pp_time t2

let rec pp_prob fmt p =
  match p with
  | PZero           -> Format.fprintf fmt "0"
  | PHalf           -> Format.fprintf fmt "1/2"
  | PTimes(q1,p1)   -> Format.fprintf fmt "%a * %a" pp_qs q1 pp_prob p1
  | PPlus(p1,p2)    -> Format.fprintf fmt "%a + %a" pp_prob p1 pp_prob p2
  | PTwoPowMinus ty -> Format.fprintf fmt "2^{-%a}" pp_ty ty
  | PUndefined   s  -> Format.fprintf fmt "&#x2207;<sub>%s</sub>" s
  | PSuccOwSpd(f,ty1, ty2,qs,t) ->
      Format.fprintf fmt "Succ^{s-pd-OW}_{%a}(skip=%a, take=%a, set-size=%a, time=%a)"
        Psym.pp f pp_ty ty1 pp_ty ty2 pp_qs qs pp_time t
  | PSuccOw(f,t) ->
      Format.fprintf fmt "Succ^{OW}_{%a}(time=%a)"
        Psym.pp f pp_time t