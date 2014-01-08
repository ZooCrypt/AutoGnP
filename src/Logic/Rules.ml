open Game
open CoreRules
open Expr
open Norm
open Util

(** Logical rules built on top of core rules. *)
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
  | _ -> ([ split_unknown e ], None)

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
  | _ -> fail_rule "rlet_unfold: no let at given position"


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
      | _ -> fail_rule "rassm : can not infer subtitution")
      subst c jc in
  rassm_decision dir subst assm ju

let t_seq t1 t2 ju = 
  List.flatten (List.map t2 (t1 ju))

let rec t_lseq ts ju =
  match ts with
  | [] -> [ju]
  | t :: ts -> t_seq t (t_lseq ts) ju

(* merging event in the postcondition *)
let merge_ev tomerge ju = 
  let tomerge = List.sort Pervasives.compare tomerge in
  let rec tac k tomerge ju = 
    match tomerge with
    | [] | [_]-> [ju]
    | i::j::tomerge -> 
      let ju' = List.hd (merge_ev (i-k) (j-k) ju) in
      tac (k+1) (j::tomerge) ju' in
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

let init_inverter test = 
  let e1, e2, bd = 
    if is_Eq test then let e1,e2 = destr_Eq test in e1,e2,[]
    else if is_Exists test then destr_Exists test 
    else raise Not_found in
  let (x1,c), z = sub e2.e_ty in
  let c = (x1, inst_ctxt c e2) in
  bd, inst_ctxt c e1, c, z

let init_inverters test = 
  let ts = destruct_Land test in
  let bds = ref [] in
  let rec aux i ts = 
    match ts with
    | [] -> []
    | t::ts ->
      try 
        let bd,e1m2,inv,z = init_inverter t in
        bds := bd @ !bds;
        (i,e1m2,inv, z, mk_V (Vsym.mk "x" e1m2.e_ty)) :: aux (i+1) ts 
      with Not_found -> aux (i+1) ts in
  let l = aux 0 ts in
  !bds, l

let last_random_indep ju = 
  match List.rev ju.ju_gdef with
  | GSamp (r,_) :: _ ->
    let ev= ju.ju_ev in
    let fv = e_vars ev in
    let bds, ms = init_inverters ev in
    let msv = List.map (fun (_,e1m2,_,_,x) -> e1m2, x) ms in
    let er = mk_V r in
    let vs = Se.elements (Se.remove er fv) in
    let vs = List.map (fun x -> x, x) vs in
    let bds = List.map (fun (x,_) -> let e = mk_V x in e, e) bds in
    let inv = 
      try Deduc.invert (vs@bds@msv) er 
      with Not_found -> failwith "can not find inverter" in
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
          inst_ctxt (y,inv) (inst_ctxt c p) in
        let inv = List.fold_left2 app_proj inv tomerge projs in
        vx, inv in
    let pos = match List.rev tomerge with
      | (i,_,_,_,_) :: _ -> i 
      | _ -> assert false in
    let pos = pos - (List.length tomerge - 1) in
    t_lseq 
      [ merge_ev tomergei;
        rctxt_ev ctxt pos;
        rnorm;
        rrandom_indep 
      ] ju

  | _ -> failwith "The last instruction is not a sampling"
  
  
let rrandom_indep ju = 
  try rrandom_indep ju 
  with _ ->
    last_random_indep ju
