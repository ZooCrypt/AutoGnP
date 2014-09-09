(*s Derived rules for dealing with random samplings. *)

(*i*)
open Util
open Nondet
open Type
open Syms
open Expr
open Norm
open Game
open Rules
open RewriteRules
open ParserUtil

module Ht = Hashtbl
module CR = CoreRules

(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Derived rule for random sampling} *)

let invert_ctxt (v,e) =
  let hole_occurs p =
    L.exists
      (fun (_,m) ->
         L.exists (fun (e,_) -> Se.mem (mk_V v) (e_vars e)) m)
      p
  in
  match Poly.polys_of_field_expr (CAS.norm id e) with
  | (nom, None) ->
    (*i v = v' * g + h => v' = (v - h) / g i*)
    let (g,h) = Poly.factor_out (mk_V v) nom in
    let e' = mk_FDiv (mk_FMinus (mk_V v) (Poly.exp_of_poly h))
                     (Poly.exp_of_poly g)
    in (v, e' |> Norm.norm_expr |> Norm.abbrev_ggen)
  | (nom, Some(denom)) when not (hole_occurs denom) ->
    (*i v = (v' * g + h) / denom => v' = (v * denom - h) / g i*)
    let (g,h) = Poly.factor_out (mk_V v) nom in
    let e' = mk_FDiv
               (mk_FMinus (mk_FMult [mk_V v; Poly.exp_of_poly denom]) (Poly.exp_of_poly h))
               (Poly.exp_of_poly g)
    in (v, e' |> Norm.norm_expr |> Norm.abbrev_ggen)
  | (_nom, Some(_denom)) ->
    tacerror "invert does not support denominators with hole-occurences in contexts"

let parse_ctxt ts ju ty (sv,se) =
  let vmap = vmap_of_globals ju.ju_gdef in
  (* bound name overshadows names in game *)
  let v = Vsym.mk sv ty in
  Hashtbl.add vmap sv v;
  (v,expr_of_parse_expr vmap ts se)

let subst_ineq ju rv e =
  let ineqs = ref [] in
  let add_ineq e =
    if is_Not e then (
      let e = destr_Not e in
      if is_Eq e then (
         let (e1,e2) = destr_Eq e in
         if (ty_equal e1.e_ty mk_Fq) then (
           let e = mk_FMinus e1 e2 in
           if not (List.mem e !ineqs) then ineqs := e::!ineqs;
         )
      )
    )
  in
  let add_ineqs e =
    L.iter add_ineq (e_ty_outermost mk_Bool e)
  in
  iter_gdef_exp add_ineqs ju.ju_gdef;
  mconcat !ineqs >>= fun ie ->
  let inter = Se.inter (e_vars ie) (e_vars e) in
  mconcat (Se.elements inter) >>= fun iv ->
  eprintf  "ineq rewrite: replace %a by %a in expression %a\n%!" pp_exp iv pp_exp ie pp_exp e;
  let erv = mk_V rv in
  let erv' = mk_V (Vsym.mk "x____" erv.e_ty) in
  let eq = Norm.norm_expr (mk_FMinus (e_replace erv erv' e) (e_replace iv ie e)) in
  guard (is_FPlus eq) >>= fun _ ->
  eprintf  "ineq rewrite: solve %a for %a\n%!" pp_exp eq pp_exp erv';
  let es = destr_FPlus eq in
  let (with_erv,without_erv) = L.partition (fun t -> Se.mem erv (e_vars t)) es in
  (match with_erv with
  | [ e ] ->
    if e_equal e (mk_FOpp erv) then ret (mk_FPlus without_erv)
    else if e_equal e erv then ret (mk_FOpp (mk_FPlus without_erv))
    else mempty
  | _ -> mempty
  ) >>= fun e ->
  ret (e_replace erv' erv e)

let transform_expr ju rv rvs e =
  let gvars = Game.write_gcmds ju.ju_gdef in
  let rves = L.map mk_V rvs in
  let evs = e_vars e in
  let factor_out_vars = rves @ (Se.elements (Se.diff evs gvars)) in
  mconcat (sorted_nub e_compare factor_out_vars) >>= fun v ->
  guard (ty_equal e.e_ty mk_Fq) >>= fun _ ->
  match Poly.polys_of_field_expr (CAS.norm id e) with
  | (nom, None) ->
    begin try
      (*i v = v' * g + h => v' = (v - h) / g i*)
      let (g,_h) = Poly.factor_out v nom in
      let e' = (Poly.exp_of_poly g) in
      guard (Se.mem (mk_V rv) (e_vars e')) >>= fun _ ->
      eprintf "transform expr=%a -> %a@\n%!" pp_exp e pp_exp e';
      ret e'
    with
      _ -> mempty
    end
  | _ -> mempty

let contexts ju rv rvs =
  (* find field expressions containing the sampled variable *)
  let es = ref [] in
  let add_subterms e =
    L.iter
      (fun fe ->
        if Se.mem (mk_V rv) (e_vars fe) && not (List.mem fe !es)
        then es := !es @ [fe])
      (e_ty_outermost mk_Fq e)
  in
  iter_gdef_exp add_subterms ju.ju_gdef;
  add_subterms ju.ju_ev;
  mconcat !es >>= fun e ->
  (* eprintf "possible expr=%a@\n%!" pp_exp e; *)
  guard (not (e_equal e (mk_V rv))) >>= fun _ ->
  mplus (ret e) (transform_expr ju rv rvs e) >>= fun e ->
  mplus (ret e) (subst_ineq ju rv e) >>= fun e ->
  ret e

let t_rnd_pos ts mctxt1 mctxt2 ty rv rvs i ju = 
  (match mctxt2 with
  | Some (sv2,se2) -> ret (parse_ctxt ts ju ty (sv2,se2))
  | None           ->
    let e2s = run (-1) (contexts ju rv rvs) in
    mconcat (sorted_nub e_compare (L.map Norm.norm_expr e2s)) >>= fun e2 ->
    ret (rv,e2)
  ) >>= fun ((v2,e2)) ->
  eprintf "trying %a -> %a@\n%!" Vsym.pp v2 pp_exp e2;
  (match mctxt1 with
  | Some(sv1,e1) -> ret (parse_ctxt ts ju ty (sv1,e1))
  | None when ty_equal ty mk_Fq ->
    begin try
      ret (invert_ctxt (v2,e2))
    with
      _ -> eprintf "invert failed\n%!"; mempty
    end
  | None -> mempty
  ) >>= fun (v1,e1) ->
  (* eprintf "calling rrnd %i on @\n%a@\n%!" i pp_ju ju; *)
  CR.t_random i (v1,e1) (v2,e2) ju

let t_rnd_maybe ts mi mctxt1 mctxt2 ju =
  let samps = samplings ju.ju_gdef in
  let rvs = L.map (fun (_,(rv,_)) -> rv) samps in
  (match mi with
  | Some i -> ret i
  | None   -> mconcat (L.map fst samps)
  ) >>= fun i ->
  let (rv,(ty,_)) = L.assoc i samps in
  eprintf "sampling: %i, %a@\n%!" i Vsym.pp rv;
  let rnd i = t_rnd_pos ts mctxt1 mctxt2 ty rv rvs i in
  ( t_debug (fsprintf "initial i is %i\n" i) @>
    t_swap_max ToEnd i rv @>= (fun i ->
    t_debug (fsprintf "after swapping toEnd: %i\n" i) @>
    t_swap_others_max ToFront i @>= (fun i ->
    t_debug (fsprintf "after swapping others ToFront: %i\n" i) @>
    rnd i)))
  ju

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Rules for random independence} *)
    
(** Merging equalities in conjuncts of event. *)
let t_merge_ev tomerge ju = 
  let tomerge = List.sort Pervasives.compare tomerge in
  let rec tac k tomerge ju = 
    match tomerge with
    | [] | [_]-> CR.t_id ju
    | i::j::tomerge -> 
      (CR.t_merge_ev (i-k) (j-k) @> tac (k+1) (j::tomerge)) ju in
  tac 0 tomerge ju

(** A tactic to automate random independence. *)

(*i We known a set of facts 
   e1 = e2 
   exists x in L | e1 = e2 
   and inequalities 
   We collect all the term we known and we try to invert the term we want.
   Assume we known e1 = e2 then we known e1 - e2 = 0
   as well for exists x in L | e1 = e2
   Then we try to invert the random variable, using the equality.
   We get an inverter.
   We look the equality which are used and we merge then in a single equivalent
   equality, again we build the inverter (this should works).
   We apply the inverter.
i*)

let simp_group e c =
  if Type.is_G e.e_ty then
    norm_expr (mk_GLog e), (fst c, mk_GLog (snd c))
  else
    e, c

let simp_div er e c =
  if Type.is_Fq e.e_ty && is_FDiv e && not (Se.mem er (e_vars (snd (destr_FDiv e)))) then
    let (num,denom) = destr_FDiv e in
    let c = (fst c, mk_FMult [snd c; denom]) in
    num, c
  else
    e, c

let simp_plus er e c =
  let er_occurs e = Se.mem er (e_vars e) in
  if is_FPlus e then
    let (er_es, no_er_es) = L.partition er_occurs (destr_FPlus e) in
    let c = (fst c, mk_FMinus (snd c) (mk_FPlus no_er_es)) in
    match er_es with
    | [] -> e, c
    | _  -> mk_FPlus er_es, c
  else
    e, c

let simp_xor er e c =
  let er_occurs e = Se.mem er (e_vars e) in
  if is_Xor e then
    let (er_es, no_er_es) = L.partition er_occurs (destr_Xor e) in
    begin match er_es with
    | [er'] ->
      assert (e_equal er' er);
      let c = (fst c, mk_Xor ([snd c]@no_er_es)) in
      er, c
    | _ ->
      e,c
    end
  else
    e, c

let simp_mult er e c =
  let er_occurs e = Se.mem er (e_vars e) in
  if Type.is_Fq e.e_ty && Type.is_Fq er.e_ty then (
    let coeff = norm_expr (mk_FDiv e er) in
    if er_occurs coeff
    then e, c
    else er, (fst c, mk_FDiv (snd c) coeff)
  ) else ( e, c )


let init_inverter test er =
  let e1, e2, bd =
    if is_Eq test then let e1,e2 = destr_Eq test in e1,e2,[]
    else if is_Exists test then destr_Exists test
    else raise Not_found
  in
  let vs = Vsym.mk "x" er.e_ty in
  Util.eprintf "checking er = %a, e1 = %a, e2 = %a\n" pp_exp er pp_exp e1 pp_exp e2;
  if e_equal e1 er && Type.ty_equal er.e_ty Type.mk_Bool then (
    ([], er, (vs, mk_Xor [mk_V vs; e2]), mk_False)
  ) else if e_equal e2 er && Type.ty_equal er.e_ty Type.mk_Bool then (
    ([], er, (vs, mk_Xor [mk_V vs; e1]), mk_False)
  ) else (
    let (x1,c), z = sub e2.e_ty in
    let c = (x1, inst_ctxt c e2) in
    let e = norm_expr (inst_ctxt c e1) in
    let (e, c) = simp_group e c in
    let (e, c) = simp_xor er e c in
    let (e, c) = simp_div er e c in
    let (e, c) = simp_plus er e c in
    let (e, c) = simp_mult er e c in
    (bd, e, c, z)
  )

let init_inverters test er =
  let ts = destruct_Land test in
  let bds = ref [] in
  let rec aux i ts =
    match ts with
    | [] -> []
    | t::ts ->
      try 
        let bd,e1me2,inv,z = init_inverter t er in
        bds := bd @ !bds;
        (i,e1me2,inv, z, mk_V (Vsym.mk "x" e1me2.e_ty)) :: aux (i+1) ts
      with Not_found -> aux (i+1) ts in
  let l = aux 0 ts in
  !bds, l

let t_last_random_indep ju = 
  match List.rev ju.ju_gdef with
  | Game.GSamp (r,_) :: _ ->
    let ev = ju.ju_ev in
    let fv = e_vars ev in
    let er = mk_V r in
    let bds, ms = init_inverters ev er in
    let msv = List.map (fun (_,e1me2,_,_,x) -> e1me2, x) ms in
    let vs = L.map (fun x -> x, x) (Se.elements (Se.remove er fv)) in
    let bds = List.map (fun (x,_) -> let e = mk_V x in e, e) bds in
    begin match exc_to_opt (fun () -> Deduc.invert (vs@bds@msv) er) with
    | None -> CR.t_fail "cannot find inverter" ju
    | Some inv ->
      let used = e_vars inv in
      let tomerge = List.filter (fun (_,_,_,_,x) -> Se.mem x used) ms in
      let tomergei = List.map (fun (i,_,_,_,_) -> i) tomerge in 
      let ctxt =
        if List.length tomerge = 1 then
          let  (_,_,c,_,x1) = List.hd tomerge in
          let x = destr_V x1 in
          fst c, inst_ctxt (x,inv) (snd c)
        else
          let e = Expr.mk_Tuple (List.map (fun (_,e,_,_,_) -> e) tomerge) in
          let vx = Vsym.mk "x" e.e_ty in
          let x = mk_V vx in
          let projs = L.mapi (fun i _ -> mk_Proj i x) tomerge in
          let app_proj inv (_,_,c,_,y) p =
            let y = destr_V y in
            inst_ctxt (y,inv) (inst_ctxt c p)
          in
          let inv = L.fold_left2 app_proj inv tomerge projs in
          vx, inv
      in
      let pos = match L.rev tomerge with
        | (i,_,_,_,_) :: _ -> i
        | _ -> assert false
      in
      let pos = pos - (L.length tomerge - 1) in
      (t_merge_ev tomergei @>
        CR.t_ctxt_ev pos ctxt @>
        t_norm_tuple_proj  @>
        CR.t_random_indep ) ju
    end
  | _ -> CR.t_fail "The last instruction is not a sampling" ju


let t_random_indep ju =
  try
    let rec aux i rc =
      match rc with
      | Game.GSamp (_) :: rc ->
        (CR.t_swap (L.length rc) i @> CR.t_random_indep) @|
        (t_norm @> (CR.t_swap (L.length rc) i @> t_last_random_indep)) @|
        (aux (i+1) rc)
      | _ :: rc -> aux (i+1) rc
      | [] ->
        CR.t_fail "random_indep: can not find an independent random variable"
    in
    (CoreRules.t_random_indep @| aux 0 (L.rev ju.ju_gdef)) ju
  with
    Invalid_rule s -> mfail s
