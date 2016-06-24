(* * Deducibility of expressions. *)

(* ** Imports and abbreviations *)
open Abbrevs
open Type
open Util
open Expr
open ExprUtils

let mk_log level = mk_logger "Deduce.Deduc" level "Deduc.ml"
let log_i = mk_log Bolt.Level.INFO


type ctxt = { to_ : expr; known : expr He.t; mutable progress : bool; mutable sub_constr : Se.t; sub_solver : (Se.t) Hty.t; ppt : bool; do_div : bool; emaps :  Syms.EmapSym.t list}

exception Found of expr

let is_in ctxt e = is_Cnst e || He.mem ctxt.known e;;
let get ctxt e = if is_Cnst e then e else He.find ctxt.known e;;

  (* add an expression with the given inverter and also immediately
     add extractable subterms (e.g., components of tuple). *)
let rec add_known (ctxt:ctxt) e inv =
  (* we might deduce non-normalized Ifte expressions such as b?g^a:g^b *)
  let e = if is_Ifte e then Norm.norm_expr_strong e else e in
  if equal_expr e ctxt.to_ then raise (Found inv);
  if not (He.mem ctxt.known e) && not (is_Cnst e) then (
    log_i (lazy (fsprintf "@[add_known:@ @[<hov 2>%a@]@]" pp_expr e));
    He.add ctxt.known e inv;
    ctxt.progress <- true;
    add_subterms ctxt e inv
  )
and add_subterms (ctxt:ctxt) e inv =
  match e.e_node with
  | V _  | Proj _ | Cnst _ -> ()
  | Tuple es ->
    List.iteri (fun i e -> add_known ctxt e (mk_Proj i inv)) es
  | App(op, es) ->
    begin match op, es with
      | GLog g, [e]         -> add_known ctxt e (mk_GExp (mk_GGen g) inv)
      | FOpp, _             -> add_known ctxt e (mk_FOpp inv)
      | FInv, [e]           -> add_known ctxt e (mk_FInv inv)
      | Not, [e]            -> add_known ctxt e (mk_Not inv)
      | (FMinus | FDiv), _  -> ()
      | (Eq| Not | Ifte), _ -> ()
      | EMap _, _           -> ()
      | GExp _, [e1;e2] when
          not ctxt.ppt && is_GGen e1 -> add_known ctxt e2 (mk_GLog inv)
      | _, _ -> ()
    end
  | Nary _ -> ()
  | Quant(_) -> ();;



 (* Set of useful subterms that we should construct,
     also contains tuples. For examples, constructing (a,b)
     might allow us to construct h((a,b)). *)
  let add_sub_constr (ctxt:ctxt) e =
    if not (Se.mem e ctxt.sub_constr) then
      log_i (lazy (fsprintf "@[<hov>add_sub_constr:@ @[<hov 2>%a@]@]" pp_expr e));
      ctxt.sub_constr <- Se.add e ctxt.sub_constr;;
  
  let rm_sub_constr (ctxt:ctxt) e = ctxt.sub_constr <- Se.remove e ctxt.sub_constr ;;
  let reg_constr ctxt e inv = add_known ctxt e inv; rm_sub_constr ctxt e ;;


(* sub_solver contains for each type a set of (known and unknown) maximal
    subterms of the given type. These are used by the type-specific
    solvers, e.g., for Xor or Fq. *)
let add_sub_solver ctxt e =
  log_i (lazy (fsprintf "@[<hov>add_sub_solver[maybe]:@ @[<hov 2>%a@]" pp_expr e));
  match e.e_ty.ty_node with
  | BS _ | Fq | G _ | Bool ->
    if is_G e.e_ty && not ctxt.ppt then () else
      begin try
          let s = Hty.find ctxt.sub_solver e.e_ty in
          if not (Se.mem e s) then
            log_i (lazy (fsprintf "@[<hov>add_sub_solver:@ @[<hov 2>%a@]@]" pp_expr e));
          Hty.replace ctxt.sub_solver e.e_ty (Se.add e s)
        with
          Not_found ->
          log_i (lazy (fsprintf "@[add_sub_solver[create]:@ @[<hov 2>%a@]@]"
                         pp_expr e));
          Hty.add ctxt.sub_solver e.e_ty (Se.singleton e)
      end
  | TySym _ | Int | Prod _ -> ();;

let add_sub ctxt e = add_sub_solver ctxt e; add_sub_constr ctxt e;;

(* for everything except field expressions, there is no nesting in the
    normal form, we therefore require only an in_field flag *)
let rec register_subexprs ctxt in_field e =
  match e.e_node with
  | Tuple es    -> add_sub_constr ctxt e; List.iter (register_subexprs ctxt false) es
  | Quant(_,_,e1) -> add_sub ctxt e; register_subexprs ctxt true e1
  | Proj(_,e1)  -> add_sub ctxt e; (register_subexprs ctxt false) e1
  | App(op, es) ->
    begin match op with
      | (FunCall _ | RoCall _ | MapLookup _ | MapIndom _) ->
        add_sub ctxt e; List.iter (register_subexprs ctxt false) es
      | FOpp | FMinus | FInv | FDiv ->
        if not in_field then add_sub_solver ctxt e;
        List.iter (register_subexprs ctxt true) es
      | GExp _ | EMap _ ->
        (* solve_group used for ppt=true, solve_fq+construction otherwise *)
        if ctxt.ppt
        then (
          add_sub_solver ctxt e; List.iter (register_subexprs ctxt true) es;
          (* also add g^u and g^v if e=g^(b?u:v) *)
          if (is_GExp e) then (
            let (a,b) = destr_GExp e in
            if (is_Ifte b) then (
              let (c,u,v) = destr_Ifte b in
              let e1 = mk_GExp a u in
              let e2 = mk_GExp a v in
              add_sub_solver ctxt e1; add_sub_solver ctxt e2;
              add_sub_constr ctxt (mk_Ifte c e1 e2);
            )
          )
        ) else (
          add_sub_constr ctxt e; List.iter (register_subexprs ctxt false) es
        )
      | GLog _ ->
        if ctxt.ppt then add_sub_solver ctxt e
        else add_sub ctxt e; List.iter (register_subexprs ctxt false) es
      | Eq | Not | Ifte ->
        add_sub_constr ctxt e; List.iter (register_subexprs ctxt false) es
      | GInv -> failwith "GInv cannot occur in normal-form"
      (*
      | FDiv ->
        FIXME: not the case, check where/why we need this
        failwith "FDiv cannot occur in normal-form" *)
    end
  | Nary(op,es) ->
    begin match op with
      | Lor | Land | GMult -> add_sub ctxt e; List.iter (register_subexprs ctxt false) es
      | FPlus | FMult ->
        if not in_field then add_sub_solver ctxt e; List.iter (register_subexprs ctxt true) es
      | Xor ->
        add_sub_solver ctxt e; List.iter (register_subexprs ctxt false) es
    end
  (* normal form is g^log(v) and must have been already added *)
  | V _ when is_G e.e_ty -> ()
  | V _                  -> add_sub_solver ctxt e
  | Cnst _               -> add_sub_constr ctxt e




(* Try to construct unknown useful expressions *)
let construct ctxt e =
  let construct1 e e1 mki =
    if not (is_in ctxt e) && is_in ctxt e1 then reg_constr ctxt e (mki (get ctxt e1))
  in
  let construct2 e e1 e2 mki =
    if not (is_in ctxt e) && is_in ctxt e1 && is_in ctxt e2 then
      reg_constr ctxt e (mki (get ctxt e1) (get ctxt e2))
  in
  let construct3 e e1 e2 e3 mki =
    if not (is_in ctxt e) && is_in ctxt e1 && is_in ctxt e2 && is_in ctxt e3 then
      reg_constr ctxt e (mki (get ctxt e1) (get ctxt e2) (get ctxt e3))
  in
  let constructn e es mki =
    if not (is_in ctxt e) && List.for_all (is_in ctxt) es then
      reg_constr ctxt e (mki (List.map (get ctxt) es))
  in
  let construct_div e e1 e2 =
    if not (is_in ctxt e1) && is_in ctxt e1 && is_in ctxt e2 then (
      reg_constr ctxt e (mk_FDiv (get ctxt e1) (get ctxt e2))
    );
    (* FIXME: shouldn't these cases be handled by the field solver *)
    if ctxt.do_div && is_in ctxt e && not (is_in ctxt e1) && is_in ctxt e2 then (
      add_known ctxt e1 (mk_FMult [get ctxt e; get ctxt e2]); rm_sub_constr ctxt e
    )
    (*
    if do_div && is_in ctxt e && not (is_in ctxt e2) && is_in ctxt e1 then (
      add_known ctxt e2 (mk_FMult [mk_FInv (get ctxt e); get ctxt e1]); rm_sub e
    )
    *)
  in
  let construct_app e op es =
    match op, es with
    | (FOpp | FMinus), _ -> assert false
    | Not,    [e1]       -> construct1 e e1 mk_Not
    | GLog _, [e1]       -> construct1 e e1 mk_GLog
    | FInv,   [e1]       -> construct1 e e1 mk_FInv
    | Eq,     [e1;e2]    -> construct2 e e1 e2 mk_Eq
    | EMap s, [e1;e2]    -> construct2 e e1 e2 (mk_EMap s)
    | Ifte,   [e1;e2;e3] -> construct3 e e1 e2 e3 mk_Ifte
    | FDiv,   [e1;e2]    -> construct_div e e1 e2
    | FunCall f, [e1]    -> construct1 e e1 (mk_FunCall f)
    | RoCall h, [e1]     -> construct1 e e1 (mk_RoCall h)
      (* in the PPT case, we always rely on the solver for groups *)
    | GExp _, [e1;e2] when not ctxt.ppt ->
      construct2 e e1 e2 mk_GExp
    | _, _ -> assert false
  in
    match e.e_node with
    | Proj(i, e1) -> construct1 e e1 (mk_Proj i)
    (*
    | H(h,e1)     -> construct1 e e1 (mk_H h)
    | ProjPermKey(ke,kp) -> construct1 e kp (mk_ProjPermKey ke) *)
    | Tuple es    -> constructn e es mk_Tuple
    | App(op,es)  -> construct_app e op es
    | Quant(q,b,e1) -> construct1 e e1 (mk_Quant q b)
    | Nary(op,es) ->
      begin match op with
      | Land  -> constructn e es mk_Land
      | Lor   -> constructn e es mk_Lor
      | GMult -> constructn e es mk_GMult
      | FPlus | FMult | Xor -> ()
      end
    | V _
    | Cnst _ -> reg_constr ctxt e e;;



(* Try do deduce interesting subterms for the given type using solvers *)
let solve ctxt ty subexprs =
  log_i (lazy (fsprintf "@[<hov>solve: started for type %a@]" pp_ty ty));
  if is_G ty && not ctxt.ppt then () else
    let solver, ty_rel =
      match ty.ty_node with
      | BS _ | Bool  -> DeducXor.solve_xor, equal_ty ty
      | Fq           -> DeducField.solve_fq, equal_ty ty
      | G _          -> DeducGroup.solve_group ctxt.emaps, fun t -> is_G t || is_Fq t
      | TySym _ | Prod _ | Int -> assert false
    in
    let k,u = Se.partition (is_in ctxt) subexprs in
    if Se.is_empty u then (
      log_i (lazy (fsprintf "@[<hov>solve: done for type %a@]" pp_ty ty));
      Hty.remove ctxt.sub_solver ty
    ) else (
      let k' = Se.filter (fun e -> ty_rel e.e_ty) (he_keys ctxt.known) in
      let k = Se.elements (Se.union k k') in
      let k = ref (List.map (fun e -> (e, I (get ctxt e))) k) in
      log_i (lazy (fsprintf "@[<hov>known:@ @[<hov 2>%a@]@]"
                     (pp_list "," pp_expr) (List.map fst !k)));
      log_i (lazy (fsprintf "@[<hov>unknown:@ @[<hov 2>%a@]@]"
                     (pp_list "," pp_expr) (Se.elements u)));
      Se.iter (fun u ->
          try
            let inv = solver !k u in
            add_known ctxt u (expr_of_inverter inv);
            k := (u,inv) :: !k
          with Not_found -> ()) u
    )

(* ** Deducibility function
 * ----------------------------------------------------------------------- *)


let invert' ?ppt_inverter:(ppt=false) emaps do_div known_es to_ =
  let ctxt = { to_ =  Norm.norm_expr_strong to_ ;  known = He.create 17;  progress = false;  sub_constr =  Se.empty; sub_solver = Hty.create 7; ppt = ppt; do_div=do_div; emaps = emaps} in
      (* Initialisation *)
      try
        (* initialize for all known expressions *)
        let init_known (e,I i) =
          let e = Norm.norm_expr_strong e in
          log_i (lazy (fsprintf "@[<hov>init_known:@ @[<hov 2>%a@]@]" pp_expr e));
          register_subexprs ctxt false e;
          add_known ctxt e i
        in
        List.iter init_known known_es;

        (* Register subterms of expression that we want to deduce *)
        register_subexprs ctxt false ctxt.to_;

        (* First try to construct all interesting subterms,
           if progress stops, call xor, group, or field solver *)
        while ctxt.progress do
          ctxt.progress <- false;
          Se.iter (construct ctxt) ctxt.sub_constr;
          if not (ctxt.progress) then Hty.iter (solve ctxt) ctxt.sub_solver
        done;
        raise Not_found
      with
      | Found inv -> I inv
      | Not_found -> raise Not_found
      | e ->
        let err = Printexc.to_string e in
        let bt = Printexc.get_backtrace () in
        log_i (lazy (fsprintf "@[invert:@ %s@ %s@]" err bt)); raise e

   

(* ** Wrapper function
 * ----------------------------------------------------------------------- *)

let invert ?ppt_inverter:(ppt=false) ts known_es to_ =
  let open TheoryTypes in
  let emaps = L.map snd (Mstring.bindings ts.ts_emdecls) in
  invert' ~ppt_inverter:ppt emaps false known_es to_




(* Function initialising the knowledge and the goals *)
