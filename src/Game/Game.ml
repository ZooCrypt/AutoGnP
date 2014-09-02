(** Cryptographic game definitions. *)

(*i*)
open Util
open Type
open Expr
open Syms
open Gsyms
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Types} *)

(** Variable, adversary, oracle, and hash symbol. *)
type vs  = Vsym.t
type ads = Asym.t
type os  = Osym.t
type hs  = Hsym.t

(** (Excepted) Distributions for sampling. *)
type distr = ty * expr list  (*r uniform distribution over type $t$ except for given values *)

(** List monad command for oracle definition. *)
type lcmd =
  | LLet   of vs * expr    (*r $LLet(\vec{x},e): \text{let }(x_1,..,x_k) = e$ *)
  | LBind  of vs list * hs (*r $LBind(\vec{x}, h): (x_1,..,x_k) \leftarrow L_h$ *)
  | LSamp  of vs * distr   (*r $LSamp(x,d): x \leftarrow_{\$} d$ *)
  | LGuard of expr         (*r $LGuard(t): t$ *)


(** Oracle definition. *)
type odef = os * vs list * lcmd list * Expr.expr (*r
  $(o,\vec{x}, \vec{m},e): o(x_1,..,x_l) = [e | m_1, .., m_k]$ *)

(** Game command. *)
type gcmd =
  | GLet  of vs * expr (*r $GLet(\vec{x},e): let (x_1,..,x_k) = e$ *)
  | GSamp of vs * distr     (*r $GSamp(x,d): x \leftarrow_{\$} d$ *)
  | GCall of vs list * ads * expr * odef list (*r
      $GCall(\vec{x}, e, \vec{o}): (x_1,..,x_k) \leftarrow A(e) \text{ with }o_1,..,o_l$ *)

(** Game definition. *)
type gdef = gcmd list

(** An event is just an expression. *)
type ev = expr

(** A judgment consists of a game and an event. *)
type judgment = { ju_gdef : gdef; ju_ev : ev }
  (*i FIXME: add probability tag i*)


(*i*)
(* ----------------------------------------------------------------------- *)
(** {2 Pretty printing} *)

let pp_distr fmt (ty,es) = 
  match es with
  | [] -> pp_ty fmt ty
  | _  -> F.fprintf fmt "@[<hov 2>%a \\ {@[<hov 0>%a}@]@]" pp_ty ty
            (pp_list "," pp_exp) es

(*let pp_v fmt v = F.fprintf fmt "%a_%i" Vsym.pp v (Id.tag v.Vsym.id) *)
let pp_v fmt v = Vsym.pp fmt v 

let pp_binder fmt vs = match vs with
  | [v] -> pp_v fmt v
  | _   -> F.fprintf fmt "(@[<hov 0>%a@])" (pp_list "," pp_v) vs

let pp_lcmd fmt lc = 
  match lc with
  | LLet(vs,e)  -> 
    F.fprintf fmt "@[<hov 2>let %a =@ %a@]" pp_binder [vs] pp_exp e
  | LBind(vs,h) -> 
    F.fprintf fmt "@[<hov 2>%a <-@ L_%a@]" pp_binder vs Hsym.pp h
  | LSamp(v,d)  -> 
    F.fprintf fmt "@[<hov 2>%a <-$@ %a@]" pp_binder [v] pp_distr d
  | LGuard(e)   -> pp_exp fmt e

let pp_ilcmd fmt (i,lc) =
  F.fprintf fmt "%i: %a" i pp_lcmd lc

let num_list l = L.mapi (fun i a -> i+1,a) l 

let pp_lcomp fmt (e,m) =
  match m with
  | [] -> F.fprintf fmt "1: return %a;" pp_exp e
  | _  -> F.fprintf fmt "%a;@,%i: return %a;@]" 
            (pp_list ";@," pp_ilcmd) (num_list m) (L.length m) pp_exp e

let pp_odef fmt (o, vs, ms, e) =
  F.fprintf fmt "@[<v>%a %a = [@,  @[<v>%a@]@,]@]" 
    Osym.pp o pp_binder vs pp_lcomp (e,ms)

let pp_gcmd fmt gc = match gc with
  | GLet(vs,e)      -> 
    F.fprintf fmt "@[<hov 2>let %a =@ %a@]" pp_binder [vs] pp_exp e
  | GSamp(v,d)      -> 
    F.fprintf fmt "@[<hov 2>%a <-$@ %a@]" pp_binder [v] pp_distr d
  | GCall(vs,asym,e,[]) -> 
    F.fprintf fmt "@[<hov 2>%a <-@ %a(@[%a@])@]" 
      pp_binder vs Asym.pp asym pp_exp_tnp e 
  | GCall(vs,asym,e,os) -> 
    F.fprintf fmt "@[<hov 2>%a <-@ %a(@[%a@]) with@ %a@]"
      pp_binder vs Asym.pp asym 
      pp_exp_tnp e
      (pp_list ";@ " pp_odef) os

let pp_igcmd fmt (i,gc) = 
  F.fprintf fmt "@[%i: %a@]" i pp_gcmd gc 

let pp_gdef fmt gd =
  pp_list ";@." pp_igcmd fmt (num_list gd)

let pp_ju fmt ju =
  F.fprintf fmt "@[<v 0>%a;@,: %a@]" pp_gdef ju.ju_gdef pp_exp ju.ju_ev

let pp_ps fmt ps =
  let ju_idxs =
    let i = ref 0 in L.map (fun ps -> incr i; (!i, ps)) ps
  in
  let pp_ju_idx fmt (i,ju) = F.fprintf fmt "@[%i.@[ %a @]@]" i pp_ju ju in
  F.fprintf fmt "%a\n--------------------\n\n"
    (pp_list "\n\n" pp_ju_idx) ju_idxs

(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Generic functions: $map\_*\_expr$, $iter\_*\_expr$} *)

(** map *)

let map_distr_exp f (t,es) = (t, L.map f es)

let map_lcmd_exp f lcmd = match lcmd with
  | LLet(vs,e)  -> LLet(vs, f e)
  | LBind(vs,h) -> LBind(vs,h)
  | LSamp(v,d)  -> LSamp(v, map_distr_exp f d)
  | LGuard(e)   -> LGuard(f e)

let map_odef_exp f (o,vs,ms,e) =
  (o,vs,L.map (map_lcmd_exp f) ms, f e)

let map_gcmd_exp f gcmd = match gcmd with
  | GLet(vs,e)     -> GLet(vs, f e)
  | GSamp(v,d)     -> GSamp(v, map_distr_exp f d)
  | GCall(vs,asym,e,os) -> GCall(vs, asym, f e, L.map (map_odef_exp f) os)

let map_gdef_exp f gdef = L.map (map_gcmd_exp f) gdef

let map_ju_exp f ju =
  { ju_gdef = map_gdef_exp f ju.ju_gdef; ju_ev = f ju.ju_ev }

(** iter *)

let iter_distr_exp f (_,es) = L.iter f es

let iter_lcmd_exp f lcmd = match lcmd with
  | LLet(_,e)  -> f e
  | LBind(_)   -> ()
  | LSamp(_,d) -> iter_distr_exp f d
  | LGuard(e)  -> f e

let iter_odef_exp f (_o,_vs,ms,e) =
  L.iter (iter_lcmd_exp f) ms; f e

let iter_gcmd_exp f gcmd = match gcmd with
  | GLet(_,e)     -> f e
  | GSamp(_,d)    -> iter_distr_exp f d
  | GCall(_,_,e,os) -> f e; L.iter (iter_odef_exp f) os

let iter_gcmd_exp_orcl f gcmd = match gcmd with
  | GLet(_,_)     -> ()
  | GSamp(_,_)    -> ()
  | GCall(_,_,_,os) -> L.iter (iter_odef_exp f) os

let iter_gcmd_exp_no_orcl f gcmd = match gcmd with
  | GLet(_,e)     -> f e
  | GSamp(_,d)    -> iter_distr_exp f d
  | GCall(_,_,e,_) -> f e

let iter_gdef_exp f gdef =
  L.iter (iter_gcmd_exp_no_orcl f) gdef;
  L.iter (iter_gcmd_exp_orcl f) gdef

let iter_ju_exp f ju =
  iter_gdef_exp f ju.ju_gdef; f ju.ju_ev

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Positions and replacement functions} *)

type gcmd_pos = int

type odef_pos = (int * int)

type ocmd_pos = (int * int * int)

let get_ju_gcmd ju p = L.nth ju.ju_gdef p

type ju_ctxt = {
  juc_left : gdef;
  juc_right : gdef;
  juc_ev : ev
}
  
let get_ju_ctxt ju p =
  let rhd,i,tl =  split_n p ju.ju_gdef in
  i, { juc_left = rhd; juc_right = tl; juc_ev = ju.ju_ev}

let set_ju_ctxt cmds {juc_left; juc_right; juc_ev} =
  { ju_gdef = L.rev_append juc_left (cmds @ juc_right);
    ju_ev   = juc_ev }

let set_ju_gcmd ju p cmds =
  assert (p >= 0 && p < L.length ju.ju_gdef);
  let _, ctxt = get_ju_ctxt ju p in
  set_ju_ctxt cmds ctxt

let get_ju_lcmd ju (i,j,k) = 
  match get_ju_gcmd ju i with
  | GCall(_,_,_,os) ->
    let (o,vs,ms,e) = L.nth os j in
    o,vs,split_n k ms, e
  | _ -> assert false

type ju_octxt = {
  juoc_asym : ads;
  juoc_avars : vs list;
  juoc_aarg : expr;
  juoc_oleft : odef list;
  juoc_oright : odef list;    
  juoc_osym : os;
  juoc_oargs: vs list;
  juoc_return : expr;
  juoc_cleft : lcmd list;
  juoc_cright : lcmd list;
  juoc_juc : ju_ctxt
}

let get_ju_octxt ju (i,j,k) = 
  match get_ju_ctxt ju i with
  | GCall(vsa,asym,e,os), juc ->
    let rohd, (o,vs,ms,oe), otl = split_n j os in
    let rhd, i, tl = split_n k ms in
    i, { juoc_asym = asym;
         juoc_avars = vsa;
         juoc_aarg = e;
         juoc_oright =  rohd;
         juoc_oleft = otl;
         juoc_osym = o;
         juoc_oargs = vs;
         juoc_return = oe;
         juoc_cleft = rhd;
         juoc_cright = tl;
         juoc_juc = juc }
  | _ -> assert false

let set_ju_octxt lcmds c =
  let ms = L.rev_append c.juoc_cleft (lcmds @ c.juoc_cright) in
  let os = L.rev_append c.juoc_oleft
             ((c.juoc_osym,c.juoc_oargs,ms,c.juoc_return)
              :: c.juoc_oright)
  in
  let i = [GCall(c.juoc_avars, c.juoc_asym, c.juoc_aarg, os)] in
  set_ju_ctxt i c.juoc_juc

let set_ju_lcmd ju p cmds = 
  let _, ctxt = get_ju_octxt ju p in
  set_ju_octxt cmds ctxt

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Equality} *) 

let distr_equal (ty1,es1) (ty2,es2) = 
  ty_equal ty1 ty2 && list_eq_for_all2 e_equal es1 es2
  
let lcmd_equal i1 i2 = 
  match i1, i2 with
  | LLet(x1,e1), LLet(x2,e2) ->
    Vsym.equal x1 x2 && e_equal e1 e2
  | LBind(xs1,h1), LBind(xs2,h2) ->
    list_eq_for_all2 Vsym.equal xs1 xs2 && Hsym.equal h1 h2
  | LSamp(x1,d1), LSamp(x2,d2) ->
    Vsym.equal x1 x2 && distr_equal d1 d2
  | LGuard e1, LGuard e2 -> e_equal e1 e2
  | LLet _  , (LBind _ | LSamp _ | LGuard _) 
  | LBind _ , (LLet _  | LSamp _ | LGuard _) 
  | LSamp _ , (LLet _  | LBind _ | LGuard _) 
  | LGuard _, (LLet _  | LBind _ | LSamp _ ) -> false

let lcmds_equal c1 c2 = list_eq_for_all2 lcmd_equal c1 c2

let odef_equal (o1,xs1,c1,e1) (o2,xs2,c2,e2) = 
  Osym.equal o1 o2 &&
    list_eq_for_all2 Vsym.equal xs1 xs2 &&
    lcmds_equal c1 c2 &&
    e_equal e1 e2 

let gcmd_equal i1 i2 =
  match i1, i2 with
  | GLet(x1,e1), GLet(x2,e2) ->
    Vsym.equal x1 x2 && e_equal e1 e2
  | GSamp(x1,d1), GSamp(x2,d2) ->
    Vsym.equal x1 x2 && distr_equal d1 d2
  | GCall(xs1,as1,e1,os1), GCall(xs2,as2,e2,os2) ->
    list_eq_for_all2 Vsym.equal xs1 xs2 &&
      e_equal e1 e2 &&
      list_eq_for_all2 odef_equal os1 os2 &&
      Asym.equal as1 as2
  | GLet _, (GSamp _ | GCall _) 
  | GSamp _, (GLet _ | GCall _) 
  | GCall _, (GLet _ | GSamp _) -> false

let gdef_equal c1 c2 = list_eq_for_all2 gcmd_equal c1 c2

let ju_equal ju1 ju2 = 
  gdef_equal ju1.ju_gdef ju2.ju_gdef &&
    e_equal ju1.ju_ev ju2.ju_ev

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Read and write variables } *)

(** General purpose functions. *)

let fold_union f es =
  L.fold_left (fun s e -> Se.union s (f e)) Se.empty es

let add_binding xs =
  fold_union (fun x -> Se.singleton (mk_V x)) xs

(** Distributions. *)

let read_distr (_,es) = fold_union e_vars es

(** Oracle definitions. *)

let read_lcmd = function 
  | LLet(_,e) | LGuard e -> e_vars e
  | LBind _              -> Se.empty
  | LSamp(_,d)           -> read_distr d

let read_lcmds c = fold_union read_lcmd c

let write_lcmd i =
  match i with
  | LLet(x,_) | LSamp(x,_) -> Se.singleton (mk_V x) 
  | LBind (xs,_)           -> add_binding xs 
  | LGuard _               -> Se.empty

let write_lcmds c = fold_union write_lcmd c

(** We assume oracles do not overshadow variables from main. *)
let read_odef (_,xs,cmd,e) =
  let r = Se.union (read_lcmds cmd) (e_vars e) in
  let w = Se.union (add_binding xs) (write_lcmds cmd) in
  Se.diff r w 

(** Main body. *)

let read_gcmd = function
  | GLet(_,e)         -> e_vars e 
  | GSamp(_,d)        -> read_distr d
  | GCall(_,_,e,odef) -> Se.union (e_vars e) (fold_union read_odef odef)

let read_gcmds c = fold_union read_gcmd c

let write_gcmd = function
  | GLet (x,_) | GSamp (x,_) -> Se.singleton (mk_V x)
  | GCall (xs,_,_,_)         -> add_binding xs

let write_gcmds c = fold_union write_gcmd c

(** Judgments. *)

let read_ju ju = Se.union (read_gcmds ju.ju_gdef) (e_vars ju.ju_ev)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Variable occurences} *) 

let fold_union_vs f xs =
  L.fold_right Vsym.S.union (L.map f xs) Vsym.S.empty

let set_of_list vs = L.fold_right Vsym.S.add vs Vsym.S.empty

let expr_vars e =
  Se.fold (fun e s -> Vsym.S.add (destr_V e) s) (e_vars e) Vsym.S.empty

let exprs_vars es = fold_union_vs expr_vars es

let lcmd_vars = function 
  | LLet(v,e)   -> Vsym.S.add v (expr_vars e)
  | LSamp(v,d)  -> Vsym.S.add v (exprs_vars (snd d))
  | LBind(vs,_) -> set_of_list vs
  | LGuard(e)   -> expr_vars e

let lcmds_vars c = fold_union_vs lcmd_vars c

let odef_vars (_,vs,cmd,e) =
  Vsym.S.union (set_of_list vs) (Vsym.S.union (expr_vars e) (lcmds_vars cmd))

let gcmd_all_vars = function
  | GLet(v,e) -> Vsym.S.add v (expr_vars e)
  | GSamp(v,d) -> Vsym.S.add v (exprs_vars (snd d))
  | GCall(vs,_,e,odefs) ->
    Vsym.S.union
      (fold_union_vs odef_vars odefs)
      (Vsym.S.union (expr_vars e) (set_of_list vs))

let gdef_all_vars gdef = fold_union_vs gcmd_all_vars gdef

let gdef_global_vars gdef = Se.union (read_gcmds gdef) (write_gcmds gdef)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Variable renaming} *) 

let subst_v_e tov = 
  let aux e = match e.e_node with V v -> mk_V (tov v) | _ -> raise Not_found in
  e_map_top aux

let subst_v_lc tov = function
  | LLet (v, e) -> LLet(tov v, subst_v_e tov e)
  | LBind (vs,lh) -> LBind (L.map tov vs, lh)
  | LSamp(v,d) -> LSamp(tov v, map_distr_exp (subst_v_e tov) d)
  | LGuard e -> LGuard (subst_v_e tov e)

let subst_v_odef tov (o,vs,lc,e) =
  let vs = L.map tov vs in
  let lc = L.map (subst_v_lc tov) lc in
  let e = subst_v_e tov e in
  (o, vs, lc, e)

let subst_v_gc tov = function
  | GLet(v,e) -> GLet(tov v, subst_v_e tov e)
  | GSamp(v, d) -> GSamp(tov v, map_distr_exp (subst_v_e tov) d)
  | GCall(vs, asym, e, odefs) ->
    GCall(L.map tov vs, asym, subst_v_e tov e,
          L.map (subst_v_odef tov) odefs)
  
let subst_v_gdef tov = L.map (subst_v_gc tov)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Mappings from strings to variables} *) 

type vmap = (string,Vsym.t) Hashtbl.t

(** Given two variable maps $vm_1$ and $vm_2$, return a new map $vm$ and
    a variable renaming $\sigma$ such that:
    \begin{itemize}
    \item for all $s \in dom(vm_1)$, $vm(s) = vm_1(s)$
    \item for all $s \in dom(vm_2) \setminus dom(vm_1)$, $vm(s) = vm_2(s)$
    \item for all $s \in dom(vm_2) \cap dom(vm_1)$, $vm(s) = \sigma(vm_2(s))$
    \end{itemize}
*)
let merge_vmap vm1 vm2 =
  let sigma = Vsym.H.create 134 in
  let vm  = Hashtbl.copy vm1 in
  Hashtbl.iter
    (fun s vs ->
      if Hashtbl.mem vm1 s
      then Vsym.H.add sigma vs (Hashtbl.find vm1 s)
      else Hashtbl.add vm s vs) 
    vm2;
  vm, (fun vs -> try Vsym.H.find sigma vs with Not_found -> vs)

let vmap_of_vss vss =
  let vm = Hashtbl.create 134 in
  Vsym.S.iter
    (fun vs -> Hashtbl.add vm (Vsym.to_string vs) vs)
    vss;
  vm

let vmap_of_ves ves =
  let vm = Hashtbl.create 134 in
  Se.iter
    (fun v ->
      let vs = destr_V v in
      Hashtbl.add vm (Vsym.to_string vs) vs)
    ves;
  vm

let vmap_of_globals gdef = vmap_of_ves (gdef_global_vars gdef)

let vmap_of_all gdef = vmap_of_vss (gdef_all_vars gdef)

let ves_to_vss ves =
  Se.fold (fun e vss -> Vsym.S.add (destr_V e) vss) ves Vsym.S.empty

let vmap_in_orcl ju op =
  let (i,_,_) = op in
  let gdef_before =
    let rbefore, _ = cut_n i ju.ju_gdef in
    L.rev rbefore
  in
  let _,juoc = get_ju_octxt ju op in
  vmap_of_vss
    (Vsym.S.union
       (ves_to_vss (gdef_global_vars gdef_before))
       (set_of_list juoc.juoc_oargs))

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Normal forms} *) 

let norm_expr_def e = Norm.abbrev_ggen (Norm.norm_expr e)

let norm_distr ?norm:(nf=Norm.norm_expr) s (ty,es) = 
  (ty, L.map (fun e -> nf (e_subst s e)) es)

let norm_odef ?norm:(nf=Norm.norm_expr) s (o,vs,lc,e) =
  let rec aux s rc lc = 
    match lc with
    | [] -> (o,vs,L.rev rc, nf (e_subst s e))
    | LLet (v, e) :: lc' ->
      let e = nf (e_subst s e) in
      let v = mk_V v in
      let s = Me.add v e s in
      aux s rc lc' 
    | (LBind (vs,_) as i)::lc' -> 
      let s = L.fold_left (fun s v -> Me.remove (mk_V v) s) s vs in
      aux s (i::rc) lc'
    | LSamp(v,d)::lc' ->
      let d = norm_distr ~norm:nf s d in
      let s = Me.remove (mk_V v) s in
      aux s (LSamp(v,d)::rc) lc'
    | LGuard e::lc' ->
      aux s (LGuard (nf (e_subst s e)) :: rc) lc' in
  aux s [] lc
    
let norm_gdef ?norm:(nf=Norm.norm_expr) g =
  let rec aux s rc lc = 
    match lc with
    | [] -> L.rev rc, s
    | GLet(v,e) :: lc' ->
      let e = nf (e_subst s e) in
      let v = mk_V v in
      let s = Me.add v e s in
      aux s rc lc'
    | GSamp(v, d) :: lc' ->
      let d = norm_distr ~norm:nf s d in
      let s = Me.remove (mk_V v) s in
      aux s (GSamp(v,d) :: rc) lc'
    | GCall(vs, asym, e, odefs) :: lc'->
      let e = nf (e_subst s e) in
      let odefs = L.map (norm_odef ~norm:nf s) odefs in
      let s = L.fold_left (fun s v -> Me.remove (mk_V v) s) s vs in
      aux s (GCall(vs, asym, e, odefs)::rc) lc'
  in
  aux Me.empty [] g

let norm_ju ?norm:(nf=Norm.norm_expr) ju =
  let g,s = norm_gdef ~norm:nf ju.ju_gdef in
  { ju_gdef = g;
    ju_ev = nf (e_subst s ju.ju_ev) }

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Probabilistic polynomial time} *)

let has_log_distr (_,es) = L.exists has_log es
  
let has_log_lcmd = function
  | LLet(_,e) | LGuard e -> has_log e
  | LBind _              -> false
  | LSamp(_,d)           -> has_log_distr d

let has_log_lcmds c = L.exists has_log_lcmd c

let has_log_o (_,_,c,e) = has_log e || has_log_lcmds c

let has_log_gcmd = function
  | GLet(_,e)       -> has_log e
  | GSamp(_,d)      -> has_log_distr d
  | GCall(_,_,e,os) -> has_log e || L.exists has_log_o os 

let has_log_gcmds c = L.exists has_log_gcmd c

let is_ppt_distr (_,es) = L.for_all is_ppt es
  
let is_ppt_lcmd = function
  | LLet(_,e) | LGuard e -> is_ppt e
  | LBind _              -> true
  | LSamp(_,d)           -> is_ppt_distr d

let is_ppt_lcmds c = L.for_all is_ppt_lcmd c

let is_ppt_o (_,_,c,e) = is_ppt e && is_ppt_lcmds c

let is_ppt_gcmd = function
  | GLet(_,e)       -> is_ppt e
  | GSamp(_,d)      -> is_ppt_distr d
  | GCall(_,_,e,os) -> is_ppt e || L.for_all is_ppt_o os 

let is_ppt_gcmds c = L.for_all is_ppt_gcmd c

let is_ppt_ju ju = is_ppt_gcmds ju.ju_gdef && is_ppt ju.ju_ev 

let is_call = function
  | GCall _ -> true
  | _       -> false

let has_call c = L.exists is_call c
