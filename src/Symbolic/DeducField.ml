(*s Deducibility for fields *)

(*i*)
open Util
open Poly
(* open Syms *)
open Expr
open CAS
open Norm
(*i*)

(** Special purpose routine to deduce a variable [v] from an expression [e]
    assuming all other variables are known. Returns  *)
let solve_fq_vars_known e v =
  (* eprintf "solve_fq_vars e=%a v=%a\n%!" pp_exp e Vsym.pp v; *)
  let ev = mk_V v in
  let v_occurs p =
    L.exists (fun (_,m) -> L.exists (fun (e,_) -> Se.mem ev (e_vars e)) m) p
  in
  let (num,mdenom) = polys_of_field_expr (CAS.norm id e) in
  let (g,h) = factor_out ev num in
  if g <> [] then (
    match mdenom with
    | None ->
      (*i v = v' * g + h => v' = (v - h) / g i*)
      let e' = mk_FDiv (mk_FMinus ev (exp_of_poly h)) (exp_of_poly g) in
      Game.norm_expr_def e'
    | Some(denom) when not (v_occurs denom) ->
      (*i v = (v' * g + h) / denom => v' = (v * denom - h) / g i*)
      let (g,h) = factor_out ev num in
      let e' = mk_FDiv
                 (mk_FMinus (mk_FMult [ev; exp_of_poly denom]) (exp_of_poly h))
                 (exp_of_poly g)
      in
      Game.norm_expr_def e'
    | Some(_denom) ->
      raise Not_found
  ) else (
    raise Not_found
  )


let solve_fq_var (ecs : (expr * inverter) list) e =
  if not (is_V e) then raise Not_found;
  let v = destr_V e in
  let ecs_v,ecs_poly = L.partition (fun (e,_w) -> is_V e || is_H e) ecs in
  match L.filter (fun (f,_) -> Se.mem e (e_vars f)) ecs_poly with
  | [(f,w_f)] ->
    (* if not (L.for_all (fun (e,_w) -> is_V e) ecs_v) then raise Not_found; *)
    (* eprintf "solve_fq_fast e=%a\n%!" pp_exp f; *)
    (* to check {w1->x1,...,wk->xk,wk+1->f} |- v, we take f and replace
       xi by wi and v by wk+1 in f, then we know that (f - g)/h = v. *)
    let f =
      L.fold_right
        (fun (x,w) f -> e_replace x (expr_of_inverter w) f)
        ecs_v
        f
    in
    let c = solve_fq_vars_known f v in
    let c = norm_expr (e_replace e (expr_of_inverter w_f) c) in
    (* eprintf "poly is %a, solution %a\n%!" pp_exp f pp_exp c; *)
    c
  | _ -> raise Not_found

let solve_fq_poly (ecs : (expr * inverter) list) e =
  let subst =
    L.fold_right
      (fun (x,I w) m -> Me.add w x  m)
      ecs
      Me.empty
  in
  let res = e_subst subst e
  in res
  
  
let solve_fq (ecs : (expr * inverter) list) e =
  let vars = e_vars e in
  let known_vars = se_of_list (L.filter is_V (L.map fst ecs)) in
  let known_occ_vars = L.fold_right (fun e s -> Se.union s (e_vars (fst e))) ecs Se.empty in
  if Se.subset vars known_vars then (
    I (solve_fq_poly ecs e)
  ) else if not (Se.is_empty (Se.diff vars known_occ_vars)) then (
    raise Not_found
  ) else (
    try I (solve_fq_var ecs e)
    with Not_found ->
      eprintf "$$$$$$$$$$$$$ calling Sage with %a |- %a@\n"
        (pp_list "," pp_exp) (L.map fst ecs)
        pp_exp e;
      let res = norm_expr (solve_fq_sage ecs e) in
      eprintf "$$$$$$$$$$$$$ sage result %a@\n" pp_exp res;
      I res
  )
