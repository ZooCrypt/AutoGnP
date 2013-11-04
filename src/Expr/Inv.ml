open Type
open Expr

exception Found of expr 

let solve_Fq _k _u = raise Not_found 

let invert from to_ =

  let to_ = Norm.norm_expr to_ in
  let known = He.create 17 in
  let progress = ref false in
  let is_in e = is_some_Cnst e || He.mem known e in
  let get e = if is_some_Cnst e then e else He.find known e in
  let rec add e inv =
    if e_equal e to_ then raise (Found inv);
    if not (He.mem known e) && not (is_some_Cnst e) then begin
      He.add known e inv;
      progress := true;
      add_inverter e inv
    end
  and add_inverter e inv =
    match e.e_node with
    | V _  | H _ | Proj _ | Cnst _ | ElemH _ -> ()
    | Tuple es -> 
      List.iteri (fun i e -> add e (mk_Proj i inv)) es
    | App(op, es) ->
      begin match op, es with 
      | GExp, [e1;e2] ->
        if is_GGen e1 then add e2 (mk_GLog inv)
      | GLog g, [e] -> add e (mk_GExp (mk_GGen g) inv)
      | FOpp, _ -> add e (mk_FOpp inv)
      | FInv, [e] -> add e (mk_FInv inv)
      | Not, [e] -> add e (mk_Not inv)
      | (FMinus | FDiv), _ -> ()
      | (Eq| Not | Ifte), _ -> ()
      | EMap _, _ -> ()
      | _, _ -> ()
      end
    | Nary _ -> () in

  (* sub is the list of all known subterm, on with we will apply do_construct *)
  let sub = ref Se.empty in
  let add_expr e = if not (Se.mem e !sub) then sub := Se.add e !sub in
  (* tytbl is a map associating to interesting type a set of subterm of this
     type, we will call the  *)
  let tytbl = Hty.create 7 in
  let add_base e = 
    let add e = 
      try 
        let s = Hty.find tytbl e.e_ty in
        if not (Se.mem e s) then Hty.replace tytbl e.e_ty (Se.add e s)
      with Not_found -> Hty.add tytbl e.e_ty (Se.singleton e) in
    match e.e_ty.ty_node with
    | BS _ | Fq -> add e
    | _ -> () in
  let add_base_expr e = add_expr e; add_base e in
  let rec build_tbl f e = 
    match e.e_node with
    | V _ -> add_base e
    | H(_,e1) -> add_base_expr e; build_tbl false e1
    | Tuple es -> add_expr e; List.iter (build_tbl false) es
    | Proj(_,e1) -> add_base_expr e; (build_tbl false) e1
    | Cnst _ -> ()
    | App(op, es) -> 
      begin match op with
      | FOpp | FMinus -> 
        if not f then add_base e;
        List.iter (build_tbl true) es 
      | _ -> 
        add_expr e; List.iter (build_tbl false) es
      end
    | Nary(op,es) ->
      begin match op with
      | Land | GMult-> add_expr e; List.iter (build_tbl false) es
      | FPlus | FMult -> add_base e; List.iter (build_tbl true) es
      | Xor -> add_base e; List.iter (build_tbl false) es
      end
    | ElemH _ -> () in

  (* Try to reconstruct unknown expression from the set of known expression *)
  let rm_sub e = sub := Se.remove e !sub in
  let add_rm e inv = add e inv; rm_sub e in
  let construct1 e e1 mki =
    if not (is_in e) && is_in e1 then add_rm e (mki (get e1)) in
  let do_construct e = 
    match e.e_node with
    | V _ -> ()
    | Cnst _ -> ()
    | Proj(i, e1) -> construct1 e e1 (mk_Proj i)
    | H(h,e1)     -> construct1 e e1 (mk_H h)
    | Tuple es ->
      if not (is_in e) && List.for_all is_in es then
        add_rm e (mk_Tuple (List.map get es))
    | App(op,es) ->
      begin match op, es with
      | GExp, [e1;e2] ->
        if not (is_in e) && is_in e1 && is_in e2 then 
          add_rm e (mk_GExp (get e1) (get e2))
      | GLog _, [e1] -> construct1 e e1 mk_GLog
      | FOpp, _   -> assert false 
      | FMinus, _ -> assert false
      | FInv, [e1] -> construct1 e e1 mk_FInv
      | FDiv, [e1;e2] ->
        if is_in e then
          if is_in e1 then
            (if not (is_in e2) then 
                (* We should check that e1 is not 0 *)
                (add e2 (mk_FMult [mk_FInv (get e); get e1]);
                 rm_sub e))
          else 
            (if is_in e2 then (add e1 (mk_FMult [get e; get e2]); rm_sub e))
        else
          if is_in e1 && is_in e2 then add_rm e (mk_FDiv (get e1) (get e2))
      | Eq, [e1;e2] ->
        if not (is_in e) && is_in e1 && is_in e2 then
          add_rm e (mk_Eq (get e1) (get e2))
      | Not, [e1] -> construct1 e e1 mk_Not
      | Ifte, ([e1;e2;e3] as es) ->
        if not (is_in e) && List.for_all is_in es then
          add_rm e (mk_Ifte (get e1) (get e2) (get e3))
      | EMap s, [e1;e2] ->
        if not (is_in e) && is_in e1 && is_in e2 then
          add_rm e (mk_EMap s (get e1) (get e2))
      | _ -> assert false
      end
    | Nary(op,es) ->
      begin match op with
      | FPlus | FMult | Xor -> () 
      | Land -> 
        if List.for_all is_in es then add_rm e (mk_Land (List.map get es))
      | GMult -> 
        if List.for_all is_in es then add_rm e (mk_GMult (List.map get es))
      end
    | ElemH _ -> () (* How to deal with this *)
  in
 
  (* Calling the solver *)
  let do_solver ty s = 
    match ty.ty_node with
    | BS _ -> 
      let k,u = Se.partition is_in s in
      if Se.is_empty u then Hty.remove tytbl ty
      else
        let k = Se.elements k in
        let k = ref (List.map (fun e -> get e, e) k) in
        Se.iter (fun u ->
          try 
            let inv = CAS.solve_xor !k u in
            add u inv;
            k := (inv, u) :: !k
          with Not_found -> ()) u
    | Fq ->
      let k,u = Se.partition is_in s in
      if Se.is_empty u then Hty.remove tytbl ty 
      else
        let k = Se.elements k in
        let k = ref (List.map (fun e -> e, get e) k) in
        Se.iter (fun u ->
          try 
            let inv = solve_Fq !k u in
            add u inv;
            k := (u,inv) :: !k
          with Not_found -> ()) u
    | _ -> assert false in

  (* Initialisation *)
    try
      let init_from (e,i) =
        let e = Norm.norm_expr e in
        build_tbl false e;
        add e i in
      List.iter init_from from;
      build_tbl false to_;    
      while !progress do
        progress := false;
        Se.iter do_construct !sub;
        if not (!progress) then Hty.iter do_solver tytbl 
      done;
      raise Not_found 
    with Found inv -> inv

 

    
    
