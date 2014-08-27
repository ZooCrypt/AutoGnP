open Game
open CoreRules
open Expr
open Norm
open Util

(** {1 Composition tactic } *)

let ( @. ) = t_seq 
let ( @+) t ts g = 
  t_subgoal ts (t g)

let ( @| ) = t_or

(** {2 Logical rules built on top of core rules. *)

(* unfold all lets and norm *)
let t_norm ju =
  let new_ju = norm_ju ~norm:norm_expr_def ju in
  t_conv true new_ju ju

let t_norm_tuple_proj ju = 
  let norm e = remove_tuple_proj (norm_expr_def e) in
  let new_ju = norm_ju ~norm ju in
  t_conv true new_ju ju

(* norm without unfolding *)
let t_norm_nounfold ju = 
  let new_ju = map_ju_exp norm_expr_def ju in
  t_conv true new_ju ju


(* unfold without norm *)
let t_unfold_only ju = 
  let new_ju = norm_ju ~norm:(fun x -> x) ju in
  t_conv false new_ju ju

(* [simp e unknown] takes an exponent expression [e] and a
   set [unknown] of unknown expressions.
   It returns a pair [(ges,mdenom)] where [mdenom] is 
   a denominator using [None] to encode [1] and [ges] is a
   list of of triples (b,ue,ke) representing (b^ue)^ke
   where [None] encodes the default group generator.
   The whole list [ges] represent the product of group
   elements in [ges]. *)
let simp_exp e unknown =
  let norm_mult es = mk_FMult (List.sort e_compare es) in
  let norm_fopp e  = mk_FOpp e in
  let rec split_unknown e =
    let is_unknown e = Se.mem e unknown in
    match e.e_node with
    | Nary(FMult,es) ->
      let de,es = List.partition is_GLog es in
      let ue,ke = List.partition is_unknown es in 
      let b,de = match de with
        | []    -> (None,de)
        | b::bs -> (Some (destr_GLog b),bs)
      in
      begin match ue@de, ke with
      | [],ke -> (b, norm_mult ke,None)
      | ue,[] -> (b, norm_mult ue,None)
      | ue,ke -> (b, norm_mult ue, Some(norm_mult ke))
      end
    | App(FOpp,[a]) ->
      begin match split_unknown a with
      | (b,e1,None)    -> (b, norm_fopp e1,None)
      | (b,e1,Some e2) -> (b, e1,Some(norm_fopp e2))
      end
    | _ -> (None,e,None)
  in
  let go sum denom = (List.map split_unknown sum, denom) in
  match e.e_node with
  | Nary(FPlus,es)  -> go es None
  | App(FDiv,[a;b]) ->
    begin match a.e_node with
    | Nary(FPlus,es) -> go es (Some b)
    | _ -> ([(None,a,None)],Some b)
    end
  | _ -> ([ split_unknown e ], None)

let rewrite_exps unknown e0 =
  let rec go e =
    let e = e_sub_map go e in
    match e.e_node with
    | App(GExp _,[a;b]) ->
      assert (is_GGen a);
      let gen = a in
      let (ies,ce) = simp_exp b unknown in
      let expio b ie moe =
        let gen = match b with None -> gen | Some a -> a in
        match moe with
        | Some oe -> mk_GExp (mk_GExp gen ie) oe
        | None    -> mk_GExp gen ie
      in
      let a =
        match ies with
        | []         -> gen
        | [b,ie,moe] -> expio b ie moe
        | ies        -> mk_GMult (List.map (fun (b,ie,moe) -> expio b ie moe) ies)
      in
      begin match ce with
      | None    -> a
      | Some oe -> mk_GExp a (mk_FInv oe)
      end
    | _ -> e
  in
  go e0

(* norm and try to rewrite all exponentiations as products of
   (g^i)^o or X where i might be unknown, but o is not unknown.
   If there is a "let z=g^i" we can replace g^i by z in the next
   step. *)
let t_norm_unknown unknown ju =
  let norm e = abbrev_ggen (rewrite_exps (se_of_list unknown) (norm_expr e)) in
  let new_ju = map_ju_exp norm ju in
  t_conv true new_ju ju

let t_let_abstract p vs e ju =
  let l,r = Util.cut_n p ju.ju_gdef in
  let v = mk_V vs in
  (* could also try to normalize given expression *)
  let subst a = e_replace e v a in
  let new_ju = { ju_gdef = List.rev_append l (GLet(vs, e)::map_gdef_exp subst r);
                 ju_ev = subst ju.ju_ev }
  in
  t_conv false new_ju ju

let t_let_unfold p ju =
  match get_ju_ctxt ju p with
  | GLet(vs,e), juc ->
    let subst a = e_replace (mk_V vs) e a in
    let juc = { juc with
                juc_right = map_gdef_exp subst juc.juc_right;
                juc_ev = subst juc.juc_ev }
    in
    t_conv false (set_ju_ctxt [] juc) ju
  | _ -> tacerror "rlet_unfold: no let at given position"


let t_assm_decisional dir assm subst ju =
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
      | _ -> tacerror "assumption_decisional : can not infer substitution")
      subst c jc in
  t_assm_decision dir subst assm ju

let t_assm_computational assm ev_e ju =
  let c = assm.Assumption.ac_prefix in
  let jc = Util.take (List.length c) ju.ju_gdef in
  let subst =
    List.fold_left2 (fun s i1 i2 ->
      match i1, i2 with
      | GLet(x1,_), GLet(x2,_) | GSamp(x1,_), GSamp(x2,_) 
        when Type.ty_equal x1.Vsym.ty x2.Vsym.ty ->
        Vsym.M.add x1 x2 s
      | _ ->
        tacerror "assumption_computational : can not infer substitution")
      Vsym.M.empty c jc
  in
  t_assm_comp assm ev_e subst ju

(* merging event in the postcondition *)
let t_merge_ev tomerge ju = 
  let tomerge = List.sort Pervasives.compare tomerge in
  let rec tac k tomerge ju = 
    match tomerge with
    | [] | [_]-> t_id ju
    | i::j::tomerge -> 
      (t_merge_ev (i-k) (j-k) @. tac (k+1) (j::tomerge)) ju in
  tac 0 tomerge ju

(** A tactic to automatize Random Indep *)                            
(* We known a set of facts 
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
*)


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
    mk_FPlus er_es, c
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
  if Type.is_Fq e.e_ty then (
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
  let (x1,c), z = sub e2.e_ty in
  let c = (x1, inst_ctxt c e2) in
  let e = norm_expr (inst_ctxt c e1) in
  let (e, c) = simp_group e c in
  let (e, c) = simp_xor er e c in
  let (e, c) = simp_div er e c in
  let (e, c) = simp_plus er e c in
  let (e, c) = simp_mult er e c in
  bd, e, c, z

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
  | GSamp (r,_) :: _ ->
    let ev = ju.ju_ev in
    let fv = e_vars ev in
    let er = mk_V r in
    let bds, ms = init_inverters ev er in
    let msv = List.map (fun (_,e1me2,_,_,x) -> e1me2, x) ms in
    let vs = L.map (fun x -> x, x) (Se.elements (Se.remove er fv)) in
    let bds = List.map (fun (x,_) -> let e = mk_V x in e, e) bds in
    let inv =
      try Deduc.invert (vs@bds@msv) er
      with Not_found -> tacerror "cannot find inverter"
    in
    let used = e_vars inv in
    let tomerge = List.filter (fun (_,_,_,_,x) -> Se.mem x used) ms in
    let tomergei = List.map (fun (i,_,_,_,_) -> i) tomerge in 
    let ctxt =
      if List.length tomerge = 1 then
        let  (_,_,c,_,x1) = List.hd tomerge in
        let x = destr_V x1 in
        fst c, inst_ctxt (x,inv) (snd c)
      else
        let e = mk_Tuple (List.map (fun (_,e,_,_,_) -> e) tomerge) in
        let vx = Vsym.mk "x" e.e_ty in
        let x = mk_V vx in
        let projs = List.mapi (fun i _ -> mk_Proj i x) tomerge in
        let app_proj inv (_,_,c,_,y) p =
          let y = destr_V y in
          inst_ctxt (y,inv) (inst_ctxt c p)
        in
        let inv = List.fold_left2 app_proj inv tomerge projs in
        vx, inv
    in
    let pos = match List.rev tomerge with
      | (i,_,_,_,_) :: _ -> i
      | _ -> assert false
    in
    let pos = pos - (List.length tomerge - 1) in
    (t_merge_ev tomergei @.
      t_ctxt_ev pos ctxt @.
      t_norm_tuple_proj  @.
      t_random_indep ) ju

  | _ -> tacerror "The last instruction is not a sampling"
  
let t_random_indep ju =
  let rec aux i rc ju =
    match rc with
    | GSamp (_,_) :: rc ->
      (t_norm @. (t_swap (List.length rc) i @. t_last_random_indep) @|
       aux (i+1) rc) ju
    | _ :: rc -> aux (i+1) rc ju
    | [] -> 
      tacerror "random_indep: can not find an independent random variable" in
  (CoreRules.t_random_indep @| aux 0 (List.rev ju.ju_gdef)) ju


