(*s Derived rules for dealing with raddtest, rcase_ev, and rexcept. *)

(*i*)
open Util
open Type
open Expr
open Game
open Syms
open TheoryState
open CoreRules
open NormField

module Ht = Hashtbl
module CR = CoreRules
(*i*)

(* Useful (in)equalities that can be obtained by applying one of the three rules *)
type useful_cases =
  | AppAddTest    of ocmd_pos * expr
  | AppExceptOrcl of ocmd_pos * expr
  | AppExcept     of gcmd_pos * expr
  | AppCaseEv     of expr

let uc_exp uc = match uc with
  | AppAddTest(_,e) | AppExceptOrcl(_,e) | AppExcept(_,e) | AppCaseEv(e) -> e

let compare_uc uc1 uc2 =
  match uc1, uc2 with
  | AppAddTest(opos1,e1), AppAddTest(opos2,e2) ->
    let cmp = compare opos1 opos2 in
    if cmp <> 0 then cmp else e_compare e1 e2
  | AppExceptOrcl(opos1,e1), AppExceptOrcl(opos2,e2) ->
    let cmp = compare opos1 opos2 in
    if cmp <> 0 then cmp else e_compare e1 e2
  | AppExcept(gpos1,e1), AppExcept(gpos2,e2) ->
    let cmp = compare gpos1 gpos2 in
    if cmp <> 0 then cmp else e_compare e1 e2
  | AppCaseEv(e1), AppCaseEv(e2) ->
    e_compare e1 e2
  | AppAddTest _, _ -> 1
  | _, AppAddTest _ -> -1
  | AppExceptOrcl _, _ -> 1
  | _, AppExceptOrcl _ -> -1
  | AppExcept _, _ -> 1
  | _, AppExcept _ -> -1

let pp_useful_cases fmt uc =
  match uc with
  | AppAddTest((g_idx,oi,o_idx),e) ->
    F.fprintf fmt "app(raddtest (%i,%i,%i)) %a)" g_idx oi o_idx pp_exp e
  | AppExceptOrcl((g_idx,oi,o_idx),e) ->
    F.fprintf fmt "app(rexcept_orcl (%i,%i,%i)) %a)" g_idx oi o_idx pp_exp e
  | AppExcept(g_idx,e) ->
    F.fprintf fmt "app(rexcept (%i) %a" g_idx pp_exp e
  | AppCaseEv(e) ->
    F.fprintf fmt "app(rcase_ev %a)" pp_exp e

let is_Useless e =
  is_FNat e || (is_FOpp e && is_FNat (destr_FOpp e)) || is_H e

let compute_case cases mhidden _fbuf ctx e =
  let fes = ref Se.empty in
  e_iter_ty_maximal mk_Fq (fun e -> fes := Se.add e !fes) e;
  (* F.fprintf fbuf "@[  max_field:    %a@\n@]%!"
       (pp_list "@\n " pp_exp) (Se.elements !fes); *)
  let facs = ref Se.empty in
  L.iter
    (fun v ->
      L.iter (fun e ->
        let ve = mk_V v in
        let (num,_denom) = NormField.polys_of_field_expr (Norm.norm_expr e) in
        if Se.mem ve (e_vars e) then
          match NormField.div_factors num (EP.var ve) with
          | Some fs ->
            let fs = L.filter (fun e -> not (is_Useless e)) fs in
            facs := Se.union (se_of_list fs) !facs;
          | None -> ())
        (Se.elements !fes))
    mhidden;
  let facs = Se.diff !facs (se_of_list (ctx.ic_nonZero @ ctx.ic_isZero)) in
  let add_case e =
    (* 
    let (num,denom) = polys_of_field_expr e in
    if denom = None then (
      (* check if num solvable for random variable, then we can ensure that
         num <> 0 by applying rexcept *)
      ()
    ) else (
    *)
    (
      (* we cannot make the value non-zero, so we try to make it zero *)
      match ctx.ic_pos with
      | InEv ->
        cases := AppCaseEv(e) :: !cases
      | InMain(_gpos) ->
        (* can we do anything here? rexcept is already handled above if possible *)
        ()
      | InOrcl(gpos,oi,_opos) ->
        cases := AppAddTest((gpos,oi,0),e) :: !cases
      | InOrclReturn(gpos,oi) ->
        cases := AppAddTest((gpos,oi,0),e) :: !cases
    )
  in
  if not (Se.is_empty facs) then (
    L.iter add_case (Se.elements facs)
   (* 
    F.fprintf fbuf "@[%a;@\n@\n@]" pp_iter_ctx ctx;
    F.fprintf fbuf "@[  facs:    %a@\n@]%!"
      (pp_list ", " pp_exp) (Se.elements facs);
   *)                        
  )

let destr_Rev_Var e =
  match e.e_node with
  | App(GExp _,[e1;e2]) when is_GGen e1 && is_V e2 ->
    Some (destr_V e2)
  | _ when is_V e ->
    Some (destr_V e)
  | _ -> None
 
let maybe_hidden_rvars gdef =
  let rec go hidden gdef =
    match gdef with
    | [] -> hidden
    | GSamp(v,_) :: gdef ->
      go (v::hidden) gdef
    | GCall(_,_,e,_) :: gdef ->
      let es = if is_Tuple e then destr_Tuple e else [e] in
      let revealed_vars = catSome (L.map destr_Rev_Var es) in 
      let hidden = L.filter (fun v -> not (L.mem v revealed_vars)) hidden in
      go hidden gdef
    | _ :: gdef ->
      go hidden gdef
  in
  go [] gdef

let print_cases ts =
  let ju   =  L.hd (get_proof_state ts).subgoals in
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  let maybe_hidden = maybe_hidden_rvars ju.ju_gdef in
  let cases = ref [] in
  F.fprintf fbuf "@[maybe hidden: %a@\n@\n@]" (pp_list ", " Vsym.pp) maybe_hidden;
  (* write function that computes non-hidden variables (given out in exponent)
     and potentially hidden variables *)
  (* write function that traverses all maximal expression of type F_p together
     with position and determines useful case rule applications *)
  iter_ctx_ju_exp (compute_case cases maybe_hidden fbuf) ju;
  let cases = sorted_nub compare_uc !cases in
  (* we choose the earliest position if there are multiple occurences with the
     same expression *)
  let cases =
    group (fun uc1 uc2 -> e_equal (uc_exp uc1) (uc_exp uc2)) cases
    |> L.map L.hd
  in
  F.fprintf fbuf "@[cases: %a@\n@\n@]" (pp_list ", " pp_useful_cases) cases;
  (ts, "Here:\n\n"^(Buffer.contents buf))
