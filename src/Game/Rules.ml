open Game
open CoreRule
open Expr
open Norm
open Util

(* unfold all lets and norm *)
let rnorm ju =
  let new_ju = norm_ju ~norm:norm_expr_def ju in
  rconv true new_ju ju

(* norm without unfolding *)
let rnorm_nounfold ju = 
  let new_ju = map_ju_exp norm_expr_def ju in
  rconv true new_ju ju

(* unfold without norm *)
let runfold_only ju = 
  let new_ju = norm_ju ~norm:(fun x -> x) ju in
  rconv false new_ju ju

(* exponent rewriting *)
let simp_exp e unknown =
  let norm_mult es = mk_FMult (List.sort e_compare es) in
  let norm_fopp e  = mk_FOpp e in
  let rec split_unknown e =
    let is_unknown e = is_GLog e || Se.mem e unknown in
    match e.e_node with
    | Nary(FMult,es) ->
      (match List.partition is_unknown es with
       | [],ke -> (norm_mult ke,None)
       | ue,[] -> (norm_mult ue,None)
       | ue,ke -> (norm_mult ue,Some(norm_mult ke)))
    | App(FOpp,[a]) ->
        (match split_unknown a with
         | (e1,None)    -> (norm_fopp e1,None)
         | (e1,Some e2) -> (e1,Some(norm_fopp e2)))
    | _ -> (e,None)
  in
  let go sum denom =
    (List.map split_unknown sum, denom)
  in
  match e.e_node with
  | Nary(FPlus,es)  -> go es None
  | App(FDiv,[a;b]) ->
      (match a.e_node with
       | Nary(FPlus,es) -> go es (Some b)
       | _ -> ([a,None],Some b) )
  | _ -> ([split_unknown e ], None)

let rewrite_exps unknown e0 =
  let rec go e =
    let e = e_sub_map go e in
    match e.e_node with
    | App(GExp,[a;b]) ->
      assert (is_GGen a);
      let gen = a in
      let (ies,ce) = simp_exp b unknown in
      let expio ie moe = match moe with
        | Some oe -> mk_GExp (mk_GExp gen ie) oe
        | None    -> mk_GExp gen ie
      in
      let a =
        match ies with
        | []       -> gen
        | [ie,moe] -> expio ie moe
        | ies      -> mk_GMult (List.map (fun (ie,moe) -> expio ie moe) ies)
      in
      (match ce with
       | None    -> a
       | Some oe -> mk_GExp a (mk_FInv oe))
    | _ -> e
  in
  go e0

(* norm and try to rewrite all exponentiations as products of
   (g^i)^o or X where i might be unknown, but o is not unknown.
   If there is a "let z=g^i" we can replace g^i by z in the next
   step. *)
let rnorm_unknown unknown ju =
  let norm e = abbrev_ggen (rewrite_exps (se_of_list unknown) (norm_expr e)) in
  let new_ju = map_ju_exp norm ju in
  rconv true new_ju ju

(* FIXME: does not work for first line *)
let rlet_abstract p vs e ju =
  match get_ju_ctxt ju p with
  | cmd, juc ->
    let v = mk_V vs in
    let cmds = cmd::[GLet(vs, e)] in
    (* could also try to normalize given expression *)
    let subst a = e_replace e v a in
    let juc = { juc with
                juc_right = map_gdef_exp subst juc.juc_right;
                juc_ev = subst juc.juc_ev }
    in
    rconv false (set_ju_ctxt cmds juc) ju

let rlet_unfold p ju =
  match get_ju_ctxt ju p with
  | GLet(vs,e), juc ->
    let subst a = e_replace (mk_V vs) e a in
    let juc = { juc with
                juc_right = map_gdef_exp subst juc.juc_right;
                juc_ev = subst juc.juc_ev }
    in
    rconv false (set_ju_ctxt [] juc) ju
  | _ -> assert false


let rassm dir assm subst ju =
  let c = 
    if dir = LeftToRight then assm.Assumption.ad_prefix1 
    else assm.Assumption.ad_prefix1 in
  let jc = Util.take (List.length c) ju.ju_gdef in
  let subst = 
    List.fold_left2 (fun s i1 i2 ->
      match i1, i2 with
      | GLet(x1,_), GLet(x2,_) | GSamp(x1,_), GSamp(x2,_) 
        when Type.ty_equal x1.Vsym.ty x2.Vsym.ty ->
        Vsym.M.add x1 x2 s
      | _ -> failwith "rassm : can not infer subtitution")
      subst c jc in
  rassm_decision dir subst assm ju


let switch_eq e1 e2 = 
  let x = Vsym.mk "x" e1.e_ty in
  match e1.e_ty.ty_node with
  | BS _ -> mk_Xor [mk_V x; e2]
  | G  _ -> mk_FMinus (mk_GLog (mk_V x)) (mk_GLog e2)
  | Fq   -> mk_FMinus (mk_V x) e2
  | _    -> raise Not_found 
            (* Can we perform recursive call for product ? *)
            (* How to do with bool *)  

let auto_indep ju =
  let gs = apply rnorm ju in
  let invert_eq vars r ev =
    let re = mk_V r in
    let (e1,e2) = destr_Eq ev in
    if not (e_exists (e_equal re) e1) then raise Not_found;
    let x, inve = switch_eq e1 e2 in
    let y = Vsym.mk "y" e.e_ty in
    let inv = Inv.invert (inve, inst_ctxt (x,inve) e1 :: vars) re in
    (x, inv) in

  let find_inverter r i ev =
    if is_Eq ev then invert_eq r ev
    else if is_ElemH ev then invert_ElemH r ev 
    else raise Not_found in
  
      
    match ev with
    | 
  let ju' = List.hd (rnorm ju) in
  let can_swap
  swap pos d;
  context_select;

let rrandom_indep ju =
(*  try *) CoreRule.rrandom_indep ju 
(*  with Failure _ -> auto_indep ju *)
