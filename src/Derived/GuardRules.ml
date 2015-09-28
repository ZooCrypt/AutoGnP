(* * Guard rules (Guess) *)

(* ** Imports and abbreviations *)
open Abbrevs
open Type
open Expr
open ExprUtils
open Game
open Syms
open CoreTypes
open Nondet

module CR = CoreRules

(* ** Rule for guess
 * ----------------------------------------------------------------------- *)

let t_guess_maybe masym mvars ju =
  let se = ju.ju_se in
  let ev = se.se_ev in
  (match try Some (destr_Quant ev) with _ -> None with
   | Some (Exists,(vs,_), _) -> ret vs
   | None | Some _           -> mempty
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
  Tactic.t_guess asym vars ju
