open Abbrevs
open Type
open Game
open Syms
open CoreTypes
open Nondet

module CR = CoreRules

let t_guess_maybe _ts masym mvars ju =
  let se = ju.ju_se in
  let ev = se.se_ev in
  (match ev.ev_binding, ev.ev_quant with
    | [(vs,_)], Exists -> ret vs
    | _ -> mempty
  ) >>= fun vs ->
  let asym =
    match masym with
    | Some asym -> asym
    | None ->
      Asym.mk "CC" (mk_Prod []) (mk_Prod (L.map  (fun v -> v.Vsym.ty) vs))
  in
  let vars =
    match mvars with
    | Some vars -> vars
    | None ->
      L.map (fun v -> Vsym.mk (Id.name v.Vsym.id) v.Vsym.ty) vs
  in
  CR.t_guess asym vars ju
