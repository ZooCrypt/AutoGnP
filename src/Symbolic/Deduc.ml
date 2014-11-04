(*s Deducibility of expressions. *)

(*i*)
(* open Util *)
open Type
open Expr
(*i*)

exception Found of expr

let solve_Fq k u = DeducField.solve_fq k u

let invert' ?ppt_inverter:(ppt=false) do_div known_es to_ =
  let to_ = Norm.norm_expr to_ in
  let known = He.create 17 in
  let progress = ref false in
  let is_in e = is_some_Cnst e || He.mem known e in
  let get e = if is_some_Cnst e then e else He.find known e in

  (** add an expression with the given inverter and also immediately
      add extractable subterms (e.g., components of tuple). *)
  let rec add_known e inv =
    (* eprintf "adding %a@\n%!" pp_exp e; *)
    if e_equal e to_ then raise (Found inv);
    if not (He.mem known e) && not (is_some_Cnst e) then (
      He.add known e inv;
      progress := true;
      add_subterms e inv
    )
  and add_subterms e inv =
    match e.e_node with
    | V _  | H _ | Proj _ | Cnst _ | Exists _ -> ()
    | Tuple es -> 
      List.iteri (fun i e -> add_known e (mk_Proj i inv)) es
    | App(op, es) ->
      begin match op, es with 
      | GLog g, [e]         -> add_known e (mk_GExp (mk_GGen g) inv)
      | FOpp, _             -> add_known e (mk_FOpp inv)
      | FInv, [e]           -> add_known e (mk_FInv inv)
      | Not, [e]            -> add_known e (mk_Not inv)
      | (FMinus | FDiv), _  -> ()
      | (Eq| Not | Ifte), _ -> ()
      | EMap _, _           -> ()
      | GExp _, [e1;e2] when
        not ppt && is_GGen e1 -> add_known e2 (mk_GLog inv)
      | _, _ -> ()
      end
    | Nary _ -> ()
  in

  let sub = ref Se.empty in
  let add_sub e = if not (Se.mem e !sub) then sub := Se.add e !sub in
  let rm_sub e = sub := Se.remove e !sub in
  let add_rm e inv = add_known e inv; rm_sub e in

  (** tytbl contains for each type a set of useful subterms that might
      help to deduce [to_] *)
  let tytbl = Hty.create 7 in
  let add_base e =
    match e.e_ty.ty_node with
    | BS _ | Fq | G _ | Bool ->
      if is_G e.e_ty && not ppt then () else
      begin try 
        let s = Hty.find tytbl e.e_ty in
        if not (Se.mem e s) then Hty.replace tytbl e.e_ty (Se.add e s)
      with
        Not_found -> Hty.add tytbl e.e_ty (Se.singleton e)
      end
    | Int | Prod _ -> ()
  in
  let add_base_expr e = add_sub e; add_base e in
  let rec register_subexprs f e = 
    match e.e_node with
    | V _         -> add_base e
    | H(_,e1)     -> add_base_expr e; register_subexprs false e1
    | Tuple es    -> add_sub e; List.iter (register_subexprs false) es
    | Proj(_,e1)  -> add_base_expr e; (register_subexprs false) e1
    | App(op, es) -> 
      begin match op with
      | FOpp | FMinus -> 
        if not f then add_base e;
        List.iter (register_subexprs true) es 
      | _ -> 
        add_sub e; List.iter (register_subexprs false) es
      end
    | Nary(op,es) ->
      begin match op with
      | Land | GMult -> add_sub e; List.iter (register_subexprs false) es
      | FPlus | FMult -> if not f then add_base e; List.iter (register_subexprs true) es
      | Xor -> add_base e; List.iter (register_subexprs false) es
      end
    | Cnst _ | Exists _ -> ()
  in

  (** Try to construct unknown useful expressions *)
  let construct1 e e1 mki =
    if not (is_in e) && is_in e1 then add_rm e (mki (get e1))
  in
  let construct2 e e1 e2 mki =
    if not (is_in e) && is_in e1 && is_in e2 then
      add_rm e (mki (get e1) (get e2))
  in
  let construct3 e e1 e2 e3 mki =
    if not (is_in e) && is_in e1 && is_in e2 && is_in e3 then
      add_rm e (mki (get e1) (get e2) (get e3))
  in
  let constructn e es mki =
    if not (is_in e) && List.for_all is_in es then
      add_rm e (mki (List.map get es))
  in
  let construct_div e e1 e2 =
    if not (is_in e1) && is_in e1 && is_in e2 then (
      add_rm e (mk_FDiv (get e1) (get e2))
    );
    (* FIXME: shouldn't these cases be handled by the field solver *)
    if do_div && is_in e && not (is_in e1) && is_in e2 then (
      add_known e1 (mk_FMult [get e; get e2]); rm_sub e
    )
    (*
    if do_div && is_in e && not (is_in e2) && is_in e1 then (
      add_known e2 (mk_FMult [mk_FInv (get e); get e1]); rm_sub e
    )
    *)
  in
  let construct_app e op es =
    match op, es with
    | (FOpp | FMinus), _ -> assert false
    | Not,    [e1]       -> construct1 e e1 mk_Not
    | GLog _, [e1]       -> construct1 e e1 mk_GLog
    | FInv,   [e1]       -> construct1 e e1 mk_FInv
    | GExp _, [e1;e2]    -> construct2 e e1 e2 mk_GExp
    | Eq,     [e1;e2]    -> construct2 e e1 e2 mk_Eq
    | EMap s, [e1;e2]    -> construct2 e e1 e2 (mk_EMap s)
    | Ifte,   [e1;e2;e3] -> construct3 e e1 e2 e3 mk_Ifte
    | FDiv,   [e1;e2]    -> construct_div e e1 e2
    | _, _ -> assert false
  in
  let construct e = 
    match e.e_node with
    | Proj(i, e1) -> construct1 e e1 (mk_Proj i)
    | H(h,e1)     -> construct1 e e1 (mk_H h)
    | Tuple es    -> constructn e es mk_Tuple
    | App(op,es)  -> construct_app e op es
    | Nary(op,es) ->
      begin match op with
      | Land -> constructn e es mk_Land
      | GMult -> constructn e es mk_GMult
      | FPlus | FMult | Xor -> ()
      end
    | V _ | Cnst _ | Exists _ -> ()
  in
 
  (* Try do deduce interesting subterms for the given type using solvers *)
  let solve ty subexprs = 
    if is_G ty then () else
    let solver =
      match ty.ty_node with
      | BS _ | Bool        -> DeducXor.solve_xor
      | Fq                 -> solve_Fq
      | Prod _ | G _ | Int -> assert false
    in
    let k,u = Se.partition is_in subexprs in
    if Se.is_empty u then Hty.remove tytbl ty
    else
      let k = Se.elements k in
      let k = ref (List.map (fun e -> (e, I (get e))) k) in
      Se.iter (fun u ->
        try 
            (* eprintf "trying: solve_xor %a |- %a@\n%!"
              (pp_list "," pp_exp) (L.map fst !k) pp_exp u; *)
          let inv =  solver !k u in
          add_known u (expr_of_inverter inv);
          k := (u,inv) :: !k
        with Not_found -> ()) u
  in

  (* Initialisation *)
  try
    (** initialize for all known expressions *)
    let init_known (e,I i) =
      let e = Norm.norm_expr e in
      register_subexprs false e;
      add_known e i
    in
    List.iter init_known known_es;

    (** Register subterms of expression that we want to deduce *)
    register_subexprs false to_;

    (** First try to construct all interesting subterms,
        if progress stops, call xor or field solver *)
    while !progress do
      progress := false;
      Se.iter construct !sub;
      if not (!progress) then Hty.iter solve tytbl
    done;
    raise Not_found
    with Found inv -> inv
    
let invert ?ppt_inverter:(ppt=false) known_es to_ =
  (* first try to find a recipe without invert *)
  (* try *)
  invert' ~ppt_inverter:ppt true known_es to_
  (* with
    Not_found -> invert' ~ppt_inverter:ppt true known_es to_ *)
