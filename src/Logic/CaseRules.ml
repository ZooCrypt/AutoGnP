(*s Derived rules for dealing with [add_test], [case_ev], and [except]. *)

(*i*)
open Abbrevs
open Util
open Type
open Expr
open ExprUtils
open Game
open Gsyms
open Syms
open Nondet
open Rules
open TheoryState
open CoreTypes
open CoreRules
open NormField

module Ht = Hashtbl
module CR = CoreRules

let log_t ls = mk_logger "Logic.Derived" Bolt.Level.TRACE "CaseRules" ls
let _log_d ls = mk_logger "Logic.Derived" Bolt.Level.DEBUG "CaseRules" ls
(*i*)

(* Useful (in)equalities that can be obtained by applying one of the three rules *)
type useful_cases =
  | AppAddTest    of ocmd_pos * expr * ty * ty
  | AppExcept     of gcmd_pos * expr
  | AppCaseEv     of expr
(*i | AppExceptOrcl of ocmd_pos * expr i*)

let uc_exp uc = match uc with
  | AppAddTest(_,e,_,_) (*i | AppExceptOrcl(_,e)  i*)
  | AppExcept(_,e) | AppCaseEv(e) -> e

let compare_uc uc1 uc2 =
  match uc1, uc2 with
  | AppAddTest(opos1,e1,_,_), AppAddTest(opos2,e2,_,_) ->
    let cmp = compare opos1 opos2 in
    if cmp <> 0 then cmp else e_compare e1 e2
(*i  | AppExceptOrcl(opos1,e1), AppExceptOrcl(opos2,e2) ->
      let cmp = compare opos1 opos2 in
      if cmp <> 0 then cmp else e_compare e1 e2 i*)
  | AppExcept(gpos1,e1), AppExcept(gpos2,e2) ->
    let cmp = compare gpos1 gpos2 in
    if cmp <> 0 then cmp else e_compare e1 e2
  | AppCaseEv(e1), AppCaseEv(e2) ->
    e_compare e1 e2
  | AppAddTest _, _ -> 1
  | _, AppAddTest _ -> -1
  | AppExcept _, _ -> 1
  | _, AppExcept _ -> -1
(*i  | AppExceptOrcl _, _ -> 1
     | _, AppExceptOrcl _ -> -1 i*)

let pp_useful_cases fmt uc =
  match uc with
  | AppAddTest((g_idx,oi,o_idx),e,_,_) ->
    F.fprintf fmt "app(raddtest (%i,%i,%i)) %a)" g_idx oi o_idx pp_exp e
  | AppExcept(g_idx,e) ->
    F.fprintf fmt "app(rexcept (%i) %a)" g_idx pp_exp e
  | AppCaseEv(e) ->
    F.fprintf fmt "app(rcase_ev %a)" pp_exp e
(*i  | AppExceptOrcl((g_idx,oi,o_idx),e) ->
      F.fprintf fmt "app(rexcept_orcl (%i,%i,%i)) %a)" g_idx oi o_idx pp_exp e i*)

let is_Useless e =
  is_FNat e || (is_FOpp e && is_FNat (destr_FOpp e)) || is_H e

let compute_case gdef mhidden _fbuf ctx e =
  let cases = ref [] in
  let fes = ref Se.empty in
  e_iter_ty_maximal mk_Fq (fun e -> fes := Se.add e !fes) e;
  let facs = ref Se.empty in
  L.iter
    (fun v ->
      L.iter (fun e ->
        let ve = mk_V v in
        let (num,_denom) = NormField.polys_of_field_expr (Norm.norm_expr_weak e) in
        if Se.mem ve (e_vars e) then
          match NormField.div_factors num (EP.var ve) with
          | Some fs ->
            let fs = L.filter (fun e -> not (is_Useless e)) fs in
            facs := Se.union (se_of_list fs) !facs;
          | None -> ())
        (Se.elements !fes))
    mhidden;
  let facs = Se.diff !facs (se_of_list (ctx.ic_nonZero @ ctx.ic_isZero)) in
  let samps = samplings gdef in
  let rvars = se_of_list (L.map (fun (_,(v,_)) -> mk_V v) samps) in
  let is_invertible e =
    (not (is_Zero e)) &&
      (is_FNat e || (is_FOpp e && is_FNat (destr_FOpp e)))
  in
  (* NOTE: we could also take into account that v can be moved forward and
           the required variables could be moved forward *)
  let used_vars_defined uvs j =
    L.for_all
      (fun uv ->
        L.mem (destr_V uv)
          (catSome (L.map (fun (i,(v,_)) -> if i < j then Some(v) else None) samps)))
      (Se.elements uvs)
  in
  let add_case e =
    let (num,denom) = polys_of_field_expr e in
    if denom = None then (
      (* check if num solvable for random variable, then we can possibly
         ensure that num <> 0 by applying rexcept *)
      L.iter
        (fun (j,(v,_)) ->
          let ve = mk_V v in
          let (coeff,rem) = NormField.div_reduce num (EP.var ve) in
          let uvs = e_vars rem in
          if is_invertible coeff && used_vars_defined uvs j then (
            let exce = Norm.norm_expr_weak (mk_FDiv rem (mk_FOpp coeff)) in
            if not (is_Zero exce) then cases := AppExcept(j,exce) :: !cases
          )
        )
        samps
    );
    (* Schwartz-Zippel tells us that we cannot make the value zero in the other case *)
    if not (Se.subset (e_vars e) rvars) then (
      match ctx.ic_pos with
      | InEv                  ->
        cases := AppCaseEv(e) :: !cases
      | InOrcl((gpos,oi,opos),aty,oty) ->
        cases := AppAddTest((gpos,oi,opos),e,aty,oty) :: !cases
      | InOrclReturn((gpos,oi,opos),aty,oty) ->
        cases := AppAddTest((gpos,oi,opos),e,aty,oty) :: !cases
      | InMain(_gpos)         -> ()
        (* can we do anything above? rexcept is already handled above if possible *)
    )
  in
  if not (Se.is_empty facs) then (
    L.iter add_case (Se.elements facs)
  );
  !cases

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

let get_cases fbuf ju =
  let se = ju.ju_se in
  let maybe_hidden = maybe_hidden_rvars se.se_gdef in
  let cases = ref [] in
  F.fprintf fbuf "@[maybe hidden: %a@\n@\n@]" (pp_list ", " Vsym.pp) maybe_hidden;
  (*i write function that computes non-hidden variables (given out in exponent)
      and potentially hidden variables i*)
  (*i write function that traverses all maximal expression of type F_p together
      with position and determines useful case rule applications i*)
  iter_ctx_se_exp
    (fun ctx e ->
      let cs = compute_case se.se_gdef maybe_hidden fbuf ctx e in
      cases := cs @ !cases)
    se;
  let cases = sorted_nub compare_uc !cases in
  (* we choose the earliest position if there are multiple occurences with the
     same expression *)
  let cases =
    group (fun uc1 uc2 -> e_equal (uc_exp uc1) (uc_exp uc2)) cases
    |> L.map L.hd
  in
  cases

let print_cases ts =
  let ju   =  L.hd (get_proof_state ts).subgoals in
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  let cases = get_cases fbuf ju in
  F.fprintf fbuf "@[cases after:@\n  %a@\n@\n@]" (pp_list ",@\n  " pp_useful_cases) cases;
  (ts, "Here:\n\n"^(Buffer.contents buf))

let t_rexcept_maybe mi mes ju =
  if mes <> None
  then failwith "rexcept: placeholder for index, but not for expression not supported";
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  let cases = get_cases fbuf ju in
  let except =
    catSome (L.map (function AppExcept(i,e) -> Some(i,e) | _ -> None) cases)
  in
  mconcat except >>= fun (j,e) ->
  guard (match mi with Some i -> i = j | None -> true) >>= fun _ ->
  CoreRules.t_except j [e] ju

let simp_eq e =
  assert (is_Fq e.e_ty);
  let sort_pair (a,b) =
    if e_compare a b > 0 then (a,b) else (b,a)
  in
  let res =
    match e.e_node with
    | Nary(FPlus,[a;b]) when is_FOpp a ->
      let (e1,e2) = sort_pair (destr_FOpp a, b) in
      mk_Eq e1 e2
    | Nary(FPlus,[a;b]) when is_FOpp b ->
      let (e1,e2) = sort_pair (destr_FOpp b, a) in
      mk_Eq e1 e2
    | _ ->
      mk_Eq e mk_FZ
  in
  Norm.norm_expr_nice res

let t_case_ev_maybe ju =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  let cases = get_cases fbuf ju in
  let except = catSome (L.map (function AppCaseEv(e) -> Some(e) | _ -> None) cases) in
  mconcat except >>= fun e ->
  CoreRules.t_case_ev (simp_eq e) ju

let simp_eq_group e =
  let to_g =
    match (destr_GLog (e_find is_GLog e)).e_ty.ty_node with
    | Type.G gn ->
      (fun fe -> mk_GExp (mk_GGen gn) fe)
    | _         -> id
  in
  assert (is_Fq e.e_ty);
  let sort_pair (a,b) =
    if e_compare a b > 0 then (a,b) else (b,a)
  in
  let res =
    match e.e_node with
    | Nary(FPlus,[a;b]) when is_FOpp a ->
      let (e1,e2) = sort_pair (destr_FOpp a, b) in
      if is_H e1 && is_H e2 then
        mk_Eq e1 e2
      else
        mk_Eq (to_g e1) (to_g e2)
    | Nary(FPlus,[a;b]) when is_FOpp b ->
      let (e1,e2) = sort_pair (destr_FOpp b, a) in
      if is_H e1 && is_H e2 then
        mk_Eq e1 e2
      else
        mk_Eq (to_g e1) (to_g e2)
    | _ ->
      mk_Eq e mk_FZ
  in
  Norm.norm_expr_strong res

let case_vars = ref []

let t_add_test_maybe ju =
  let se = ju.ju_se in
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  let cases = get_cases fbuf ju in
  let destr_prod oty = match oty.ty_node with
    | Prod(tys) -> tys
    | _ -> [oty]
  in
  let except =
    L.map
      (function AppAddTest(opos,e,aty,oty) -> Some(opos,e,aty,oty) | _ -> None)
      cases
    |> catSome
  in
  mconcat except >>= fun (opos,t,aty,oty) ->
  let tys = destr_prod oty in
  let wvars = write_gcmds se.se_gdef in
  (* test must contain oracle arguments, otherwise useless for type
     of examples we consider *)
  guard (not (Se.subset (e_vars t) wvars)) >>= fun _ ->
  let test = simp_eq_group t in
  let (asym,vars) =
    try
      let (_,(asym,vars)) =
        L.find
          (fun ((opos',test'),_v) -> opos = opos' && e_equal test test')
          !case_vars
      in
      log_t (lazy "found case_ev already!");
      if not (Se.is_empty
                (Se.inter (se_of_list (L.map mk_V vars)) (write_gcmds se.se_gdef)))
      then raise Not_found;
      if L.mem asym (asym_gcmds se.se_gdef) then raise Not_found;
      log_t (lazy "occurs check OK!@\n%!");
      (asym,vars)
    with Not_found ->
      let asym = Asym.mk "BBB" aty oty in
      let vars = L.map (fun ty -> Vsym.mk (mk_name se) ty) tys in
      case_vars := ((opos,test),(asym,vars))::!case_vars;
      (asym,vars)
  in
  CoreRules.t_add_test opos test asym vars ju
