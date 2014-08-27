(** Well-formedness of games. *)

open Util
open Expr
open Type
open Game
open Norm

type wf_check_type = CheckDivZero | NoCheckDivZero

type wf_state =
  { wf_names : Sstring.t;    (* used names for variables, adversaries, and oracles *)
    wf_bvars : Vsym.S.t;     (* bound variables, never two vsyms with the same name *)
    wf_nzero : expr option } (* product of all nonzero-assumptions for field-expressions *)

let mk_wfs () = {
    wf_names = Sstring.empty;
    wf_bvars = Vsym.S.empty;
    wf_nzero = None 
  }

let ensure_name_fresh wfs name =
  if Sstring.mem name wfs.wf_names
  then failwith "duplicate name (variables, oracles, and adversaries)"
  else { wfs with wf_names = Sstring.add name wfs.wf_names }

let ensure_names_fresh wfs names =
  List.fold_left ensure_name_fresh wfs names

let ensure_varname_fresh wfs vs =
  let name = Id.name vs.Vsym.id in
  let wfs = ensure_name_fresh wfs name in
  { wfs with wf_bvars = Vsym.S.add vs wfs.wf_bvars }

let ensure_varnames_fresh wfs vs =
  List.fold_left ensure_varname_fresh wfs vs

let ty_prod vs =
  match List.map (fun vs -> vs.Vsym.ty) vs with
  | [a] -> a
  | ts  -> mk_Prod ts

let ty_of_cnst c ty =
  let ty' =
    match c with
    | B _     -> mk_Bool
    | GGen    -> (match ty.ty_node with G _ -> ty | _ -> assert false)
    | Z       -> (match ty.ty_node with BS _ -> ty | _ -> assert false)
    | FNat(_) -> mk_Fq
  in assert(ty_equal ty' ty); ty

let ty_of_nop ty = function
  | Land  -> mk_Bool
  | Xor   -> (match ty.ty_node with BS _ | Bool -> ty | _ -> assert false)
  | (FMult | FPlus) -> mk_Fq
  | GMult  -> (match ty.ty_node with G _ -> ty | _ -> assert false)

let ty_of_op ty argtys o =
  match o with
  | GExp gv  -> ([mk_G gv;mk_Fq],mk_G gv,[])
  | GLog(gv) -> ([mk_G gv],mk_Fq,[])
  | EMap(es) -> ([mk_G (es.Esym.source1); mk_G (es.Esym.source2)], mk_G (es.Esym.target),[])
  | FMinus   -> ([mk_Fq;mk_Fq],mk_Fq,[])
  | FOpp     -> ([mk_Fq],mk_Fq,[])
  | FInv     -> ([mk_Fq],mk_Fq,[0])        (* argument 0 must be nonzero *)
  | FDiv     -> ([mk_Fq; mk_Fq],mk_Fq,[1]) (* argument 1 must be nonzero *)
  | Not      -> ([mk_Bool],mk_Bool,[])
  | Ifte     -> ([mk_Bool;ty;ty],ty,[])
     (* we ignore these inequality constraints, maybe restrict first
        argument of if to boolean variable *)
  | Eq      -> (match argtys with
                | [t1;t2] when ty_equal t1 t2 -> ([t1;t2],mk_Bool,[])
                | _ -> assert false)

let rec add_ineq ctype wfs e1 e2 =
  try
    if ctype = NoCheckDivZero then (
      wf_exp CheckDivZero wfs e1;
      wf_exp CheckDivZero wfs e2;
    );
    let e1 = norm_expr e1 in
    let e2 = norm_expr e2 in
    let mk_nzero a b =
      let h =
        match a.e_node, b.e_node with
        | App(FDiv,[a1;a2]), App(FDiv,[b1;b2]) ->
          norm_expr (mk_FMinus (mk_FMult [a1;b2]) (mk_FMult [b1;a2]))
        | App(FDiv,[a1;a2]), _ ->
          norm_expr (mk_FMinus a1 (mk_FMult [b;a2]))
        | _, App(FDiv,[b1;b2]) ->
          norm_expr (mk_FMinus b1 (mk_FMult [b2;a]))
        | _ ->
          norm_expr (mk_FMinus a b)
      in
      match wfs.wf_nzero with
      | None    -> Some h
      | Some nz -> Some (mk_FMult [ h; nz])
    in
    match e1.e_ty.ty_node,e2.e_ty.ty_node with
    | Fq, Fq   -> { wfs with
                    wf_nzero = mk_nzero e1 e2 }
    | G _, G _ -> { wfs with
                    wf_nzero = mk_nzero (mk_GLog e1) (mk_GLog e2) }
    | _ -> wfs
  with
    (* we already checked well-formedness, at least with NoCheckDivZero *)
    _ -> wfs

and check_nonzero ctype wfs e =
  if ctype = NoCheckDivZero then true
  else
    (* we know e itself is division-safe *)
    match wfs.wf_nzero with
    | Some nz ->
      let e = norm_expr e in
      (* the normal form is either f/g or f for polynomials f,g *)
      begin match e.e_node with
      | App(FDiv, [a;_b]) -> CAS.mod_reduce nz a (* division-safe => b<>0 *)
      | _                 -> CAS.mod_reduce nz e (* e is polynomial *)
      end
    | None    -> false
(* TODO Remark: I think the type checking is not necessary, it is ensured by the
   smart constructor ... *)
and wf_exp ctype wfs e0 =
  let rec go e =
    let ty =
      match e.e_node with
      | Cnst c -> ty_of_cnst c e.e_ty
      | Exists(e1,e2,(vhs)) ->
        assert (List.for_all
                  (fun (v,h) -> ty_equal v.Vsym.ty h.Hsym.dom) vhs);
        let wfs = ensure_varnames_fresh wfs (List.map fst vhs) in
        wf_exp ctype wfs e2;
        wf_exp ctype wfs e1;
        assert (ty_equal e1.e_ty e2.e_ty);
        assert (ty_equal mk_Bool e.e_ty);
        mk_Bool
      | H(h,e1) ->
        ignore (go e1);
        assert (ty_equal h.Hsym.dom e1.e_ty);
        assert (ty_equal h.Hsym.codom e.e_ty);
        h.Hsym.codom
      | Proj(i,e1) ->
          ignore (go e1);
          (match e1.e_ty.ty_node with
           | Prod(ts) when List.length ts > i ->
               assert (ty_equal (List.nth ts i) e.e_ty);
               List.nth ts i
           | _ -> assert false)
      | Tuple(es) ->
        let tys = List.map go es in
        assert (es = [] || List.length es > 1);
        assert (ty_equal (mk_Prod tys) e.e_ty);
        mk_Prod tys
      | V v ->
        assert_msg (Vsym.S.mem v wfs.wf_bvars)
          (fsprintf "wf_exp: Variable %a undefined in %a"
             Vsym.pp v pp_exp e0);
        assert (ty_equal v.Vsym.ty e.e_ty);
        v.Vsym.ty
      | Nary(Land,es) ->
        let is_InEq e =
           if is_App Not e then is_App Eq (destr_Not e) else false
        in
        let destr_InEq e = destr_Eq (destr_Not e) in
        assert (ty_equal mk_Bool e.e_ty);
        let (ineqs,others) = List.partition is_InEq es in
        assert (List.for_all (fun (e :expr) -> ty_equal mk_Bool (go e)) ineqs);
        let wfs = List.fold_left (fun wfs e ->
                                    let e1,e2 = destr_InEq e in
                                    add_ineq ctype wfs e1 e2) wfs ineqs
        in
        assert (List.for_all (fun (e :expr) ->
                                wf_exp ctype wfs e;
                                ty_equal e.e_ty mk_Bool) others);
        mk_Bool
      | Nary(op,es) ->
        let rty = ty_of_nop e.e_ty op in
        assert (List.for_all (fun (e :expr) -> ty_equal rty (go e)) es);
        assert (ty_equal rty e.e_ty);
        rty
      | App(op,es) ->
        let (tys,rty,nz) = ty_of_op e.e_ty (List.map (fun e -> e.e_ty) es) op in
        assert (list_eq_for_all2 ty_equal tys (List.map go es));
        assert_msg
          (List.for_all
            (fun i -> check_nonzero ctype wfs (List.nth es i)) nz)
          (fsprintf "Cannot prove that %a nonzero" (pp_list "," pp_exp)
            (List.map (fun i -> List.nth es i) nz));
        assert (ty_equal rty e.e_ty);
        rty
    in ty
  in
  ignore (go e0); ()

let wf_lcmds ctype wfs0 odef0 =
  let rec go wfs odef = match odef with
    | [] -> wfs
    | LLet(v,e)::lcmds ->
      let wfs = ensure_varname_fresh wfs v in
      assert (ty_equal v.Vsym.ty e.e_ty);
      wf_exp ctype wfs e;
      go wfs lcmds
    | LSamp(v,(t,es))::lcmds ->
      assert (ty_equal v.Vsym.ty t &&
                List.for_all (fun e -> ty_equal t e.e_ty) es);
      List.iter (wf_exp ctype wfs) es;
      let wfs = ensure_varname_fresh wfs v in
      let v = mk_V v in
      let wfs = List.fold_left (fun wfs e -> add_ineq ctype wfs e v) wfs es in
      go wfs lcmds
    | LBind (vs,hsym)::lcmds -> 
      assert (ty_equal (ty_prod vs) hsym.Hsym.dom);
      go wfs lcmds
    | LGuard e::lcmds ->
      assert (ty_equal e.e_ty mk_Bool);
      wf_exp ctype wfs e;
      let wfs =
        match e.e_node with
        | App(Not,[eeq]) ->
            (match eeq.e_node with
             | App(Eq,[e1;e2]) -> add_ineq ctype wfs e1 e2
             | _ -> wfs)
        | _ -> wfs
      in
      go wfs lcmds
  in
  go wfs0 odef0

let wf_odef ctype wfs (osym,vs,lcmds,e) =
   assert (ty_equal osym.Osym.dom (ty_prod vs) &&
             ty_equal osym.Osym.codom e.e_ty);
   let wfs = ensure_varnames_fresh wfs vs in
   let wfs = wf_lcmds ctype wfs lcmds in
   wf_exp ctype wfs e

let wf_gdef ctype gdef0 =
  let rec go wfs gdef = match gdef with
    | [] -> wfs
    | GLet(v,e)::gcmds ->
      let wfs = ensure_varname_fresh wfs v in
      assert (ty_equal v.Vsym.ty e.e_ty);
      wf_exp ctype wfs e;
      (* FIXME: account for binding in non-zero condition *)
      go wfs gcmds
    | GSamp(v,(t,es))::gcmds ->
      assert (ty_equal v.Vsym.ty t &&
                List.for_all (fun e -> ty_equal t e.e_ty) es &&
                (not (ty_equal t mk_Bool) || es = []));
      List.iter (wf_exp ctype wfs) es;
      let wfs = ensure_varname_fresh wfs v in
      let v = mk_V v in
      let wfs = List.fold_left (fun wfs e -> add_ineq ctype wfs e v) wfs es in
      go wfs gcmds
    | GCall(vs,asym,e,os)::gcmds ->
      let wfs = ensure_varnames_fresh wfs vs in
      let wfs = ensure_name_fresh wfs (Id.name asym.Asym.id) in
      assert (ty_equal (ty_prod vs) asym.Asym.codom &&
                ty_equal asym.Asym.dom e.e_ty);
      let wfs =
        ensure_names_fresh wfs
          (List.map (fun (osym,_,_,_) -> Id.name (osym.Osym.id)) os)
      in
      List.iter (wf_odef ctype wfs) os;
      go wfs gcmds
  in
  go (mk_wfs ()) gdef0

let wf_ju ctype ju =
  let wfs = wf_gdef ctype ju.ju_gdef in
  assert (ty_equal mk_Bool ju.ju_ev.e_ty);
  wf_exp ctype wfs ju.ju_ev
