(* Games and judgments *)
open Type
open Util
open Expr

module F = Format

(* ----------------------------------------------------------------------- *)
(** {1 Types} *)

(* (excepted) distributions for sampling *)
type distr = Type.ty * Expr.expr list
  (* uniform distribution over type t except for given values *)

(* list monad command for oracle definition *)
type lcmd = LLet   of Vsym.t * Expr.expr
              (* LLet(x,e): let (x1,..,xk) = e *)
          | LBind  of Vsym.t list * Hsym.t
              (* LBind([x1;..;xk], h): (x1,..,xk) <- L_h *)
          | LSamp  of (Vsym.t * distr)
              (* LSamp(x,d): x <-$ d *)
          | LGuard of Expr.expr
              (* LGuard(t): t *)

(* oracle definition *)
type odef = Osym.t * Vsym.t list * lcmd list * Expr.expr
  (* (o,[x1;..;xl], [m1;..;mk],e): o(x1,..,xl) = [e | m1, .., mk] *)

(* game command *)
type gcmd = GLet  of Vsym.t * Expr.expr
              (* GLet([x1;..xk], e): let (x1,..,xk) = e *)
          | GSamp of Vsym.t * distr
              (* GSamp(x,d): x <-$ d *)
          | GCall of Vsym.t list * Expr.expr * odef list
              (* GCall([x1;..xk], e, [o1;..;ol]): (x1,..,xk) <- A(e) with o1,..,ol *)

(* game definition *)
type gdef = gcmd list

(* for now, an event is just an expression *)
type ev = expr

(* judgment *)
type judgment = { ju_gdef : gdef; ju_ev : ev }

(* ----------------------------------------------------------------------- *)
(** {2 Pretty printing} *)

let pp_distr fmt (ty,es) = match es with
  | [] -> pp_ty fmt ty
  | _  -> F.fprintf fmt "%a \\ {%a}" pp_ty ty
            (pp_list "," pp_exp) es

let pp_binder fmt vs = match vs with
  | [v] -> Vsym.pp fmt v
  | _   -> F.fprintf fmt "(%a)" (pp_list "," Vsym.pp) vs

let pp_lcmd fmt lc = match lc with
  | LLet(vs,e)  -> F.fprintf fmt "let %a = %a" pp_binder [vs]
                     pp_exp e
  | LBind(vs,h) -> F.fprintf fmt "%a <- L_%a" pp_binder vs
                     Hsym.pp h
  | LSamp(v,d)  -> F.fprintf fmt "%a <-$ %a" Vsym.pp v
                     pp_distr d
  | LGuard(e)   -> pp_exp fmt e

let pp_lcomp fmt (e,m) =
  match m with
  | [] -> F.fprintf fmt "[ %a ]" pp_exp e
  | _  -> F.fprintf fmt "[ %a | %a ]" pp_exp e
            (pp_list ", " pp_lcmd) m

let pp_odef fmt (o, vs, ms, e) =
  F.fprintf fmt "%a(%a) = %a" Osym.pp o pp_binder vs
    pp_lcomp (e,ms)

let pp_gcmd fmt gc = match gc with
  | GLet(vs,e)      -> F.fprintf fmt "let %a = %a" pp_binder [vs]
                         pp_exp e
  | GSamp(v,d)      -> F.fprintf fmt "%a <-$ %a" Vsym.pp v
                         pp_distr d
  | GCall(vs,e,[]) -> F.fprintf fmt "%a <- A%a" pp_binder vs pp_exp e
  | GCall(vs,e,os) -> F.fprintf fmt "%a <- A%a with @.  %a"
                        pp_binder vs pp_exp e
                        (pp_list ",@." pp_odef) os

let pp_gdef fmt gd =
  F.fprintf fmt "@[%a @]" (pp_list "@." pp_gcmd) gd

let pp_ju fmt ju =
  F.fprintf fmt "@[%a@. : %a@]" pp_gdef ju.ju_gdef pp_exp ju.ju_ev

let pp_ps fmt ps =
  let ju_idxs =
    let i = ref 0 in List.map (fun ps -> incr i; (!i, ps)) ps
  in
  let pp_ju_idx fmt (i,ju) = F.fprintf fmt "@[%i.@[ %a @]@]" i pp_ju ju in
  F.fprintf fmt "%a\n--------------------\n\n"
    (pp_list "\n\n" pp_ju_idx) ju_idxs


(* ----------------------------------------------------------------------- *)
(** {3 Generic functions: map_*_expr, iter_*_expr } *)

(** map *)

let map_distr_exp f (t,es) = (t, List.map f es)

let map_lcmd_exp f lcmd = match lcmd with
  | LLet(vs,e)  -> LLet(vs, f e)
  | LBind(vs,h) -> LBind(vs,h)
  | LSamp(v,d)  -> LSamp(v, map_distr_exp f d)
  | LGuard(e)   -> LGuard(f e)

let map_odef_exp f (o,vs,ms,e) =
  (o,vs,List.map (map_lcmd_exp f) ms, f e)

let map_gcmd_exp f gcmd = match gcmd with
  | GLet(vs,e)     -> GLet(vs, f e)
  | GSamp(v,d)     -> GSamp(v, map_distr_exp f d)
  | GCall(vs,e,os) -> GCall(vs, f e, List.map (map_odef_exp f) os)

let map_gdef_exp f gdef = List.map (map_gcmd_exp f) gdef

let map_ju_exp f ju =
  { ju_gdef = map_gdef_exp f ju.ju_gdef; ju_ev = f ju.ju_ev }

(** iter *)

let iter_distr_exp f (_,es) = List.iter f es

let iter_lcmd_exp f lcmd = match lcmd with
  | LLet(_,e)  -> f e
  | LBind(_)   -> ()
  | LSamp(_,d) -> iter_distr_exp f d
  | LGuard(e)  -> f e

let iter_odef_exp f (_o,_vs,ms,e) =
  List.iter (iter_lcmd_exp f) ms; f e

let iter_gcmd_exp f gcmd = match gcmd with
  | GLet(_,e)     -> f e
  | GSamp(_,d)    -> iter_distr_exp f d
  | GCall(_,e,os) -> f e; List.iter (iter_odef_exp f) os

let iter_gdef_exp f gdef = List.iter (iter_gcmd_exp f) gdef

let iter_ju_exp f ju =
  iter_gdef_exp f ju.ju_gdef; f ju.ju_ev

(* ----------------------------------------------------------------------- *)
(** { Read and write variables } *)

let fold_union f es =
  List.fold_left (fun s e -> Se.union s (f e)) Se.empty es

let read_distr (_,es) = fold_union e_vars es

let read_lcmd = function 
  | LLet(_,e) | LGuard e -> e_vars e
  | LBind _ -> Se.empty
  | LSamp(_,d) -> read_distr d

let read_lcmds c = fold_union read_lcmd c

let add_binding xs = 
  fold_union (fun x -> Se.singleton (mk_V x)) xs

let write_lcmd i = 
  match i with
  | LLet(x,_)  | LSamp(x,_) -> Se.singleton (mk_V x) 
  | LBind (xs,_) -> add_binding xs 
  | LGuard _ -> Se.empty

let write_lcmds c = fold_union write_lcmd c

let read_odef (_,xs,cmd,e) = 
  let r = Se.union (read_lcmds cmd) (e_vars e) in
  let w = Se.union (add_binding xs) (write_lcmds cmd) in
  Se.diff r w 

let read_gcmd = function
  | GLet(_,e) -> e_vars e 
  | GSamp(_,d) -> read_distr d
  | GCall(_,e,odef) -> 
    Se.union (e_vars e) (fold_union read_odef odef)

let read_gcmds c = fold_union read_gcmd c

let write_gcmd = function
  | GLet (x,_) | GSamp (x,_) -> Se.singleton (mk_V x)
  | GCall (xs,_,_) -> add_binding xs

let write_gcmds c = fold_union write_gcmd c

(* ----------------------------------------------------------------------- *)
(** {3 Helper functions for rules } *)

(** smart constructors *)

(* smart constructor for judgments *)
let mk_ju gd ev =
  (* FIXME: check that fvars(ev) \subseteq bindings(gd) *)
  { ju_gdef = gd; ju_ev = ev }

type gcmd_pos = int

type odef_pos = (int * int)

type ocmd_pos = (int * int * int)

let get_ju_gcmd ju p = List.nth ju.ju_gdef p

type ju_ctxt = gdef * gdef * ev
  
let get_ju_ctxt ju p = 
  let rhd,i,tl =  split_n p ju.ju_gdef in
  i, (rhd, tl, ju.ju_ev)

let set_ju_ctxt cmd (rhd,tl,ev) = 
  { ju_gdef = List.rev_append rhd (cmd @ tl);
    ju_ev   = ev }

let set_ju_gcmd ju p cmds =
  assert (p >= 0 && p < List.length ju.ju_gdef);
  let _, ctxt = get_ju_ctxt ju p in
  set_ju_ctxt cmds ctxt

let get_ju_lcmd ju (i,j,k) = 
  match get_ju_gcmd ju i with
  | GCall(_,_,os) ->
      let (o,vs,ms,e) = List.nth os j in
      o,vs,split_n k ms, e
  | _ -> assert false

let get_ju_octxt ju (i,j,k) = 
  match get_ju_ctxt ju i with
  | GCall(vsa,e,os), ctxt ->
    let rohd, (o,vs,ms,oe), otl = split_n j os in
    let rhd, i, tl = split_n k ms in
    i, (((rhd,tl), (o,vs,oe), (rohd, otl, (vsa,e))), ctxt)
  | _ -> assert false

let set_ju_octxt cmd (((rhd,tl), (o,vs,oe), (rohd, otl, (vsa,e))), ctxt) =
  let ms = List.rev_append rhd (cmd @ tl) in
  let os = List.rev_append rohd ((o,vs,ms, oe) :: otl) in
  let i = [GCall(vsa, e, os)] in
  set_ju_ctxt i ctxt

let set_ju_lcmd ju p cmds = 
  let _, ctxt = get_ju_octxt ju p in
  set_ju_octxt cmds ctxt

(* ----------------------------------------------------------------------- *)
(** {3 Rules and tactic language} *)

(** goal handling *)

let apply rule goals = match goals with
  | g::gs -> rule g @ gs
  | _ -> failwith "there are no goals"

let delay goals = match goals with
  | g::gs -> gs@[g]
  | []    -> []

(** random rule *)

let ensure_bijection c1 c2 v =
  if not (Norm.e_equalmod (inst_ctxt c2 (inst_ctxt c1 v)) v &&
          Norm.e_equalmod (inst_ctxt c1 (inst_ctxt c2 v)) v)
  then failwith "random: contexts not bijective"

(* 'random p c1 c2' takes a position p and two contexts. It first
   ensures that there is a random sampling 'x <-$ d' at position p.
   For now, its not excepted. Otherwise we have to apply c1/c2 to
   the excepted values.
   Then it checks that under the inequalities that hold at position p,
   forall x in supp(d), c2(c1(x)) = x.  *)
let rrandom p c1 c2 ju =
  match get_ju_ctxt ju p with
  | GSamp(vs,((t,[]) as d)), ctxt ->
    let v = mk_V vs in
    ensure_bijection c1 c2 v; (* FIXME: check that both contexts well-defined at given position *)
    let vs' = Vsym.mk (Id.name vs.Vsym.id) t in
    let cmds = [ GSamp(vs',d);
                 GLet(vs, inst_ctxt c1 (mk_V vs')) ]
    in
    [ set_ju_ctxt cmds ctxt]
  | _ -> failwith "random: position given is not a sampling"

(* FIXME: buggy *)
let rrandom_oracle p c1 c2 ju =
  match get_ju_octxt ju p with
  | LSamp(vs,((t,[]) as d)), ctxt ->
    let v = mk_V vs in
    ensure_bijection c1 c2 v; (* FIXME: check that both contexts well-defined at given position *)
    let vs' = Vsym.mk (Id.name vs.Vsym.id) t in
    let cmds = [ LSamp(vs',d);
                 LLet(vs, inst_ctxt c1 (mk_V vs')) ]
    in
    [ set_ju_octxt cmds ctxt]
  | _ -> failwith "random: position given is not a sampling"

(** Norm rule: conv and let-unfold for all included expressions and terms *)

let norm_expr_def e = Norm.abbrev_ggen (Norm.norm_expr e)

let norm_distr ?norm:(nf=norm_expr_def) s (ty,es) = 
  (ty, List.map (fun e -> nf (e_subst s e)) es)

let norm_odef ?norm:(nf=norm_expr_def) s (o,vs,lc,e) =
  let rec aux s rc lc = 
    match lc with
    | [] -> (o,vs,List.rev rc, nf (e_subst s e))
    | LLet (v, e) :: lc' ->
      let e = nf (e_subst s e) in
      let v = mk_V v in
      let s = Me.add v e s in
      aux s rc lc' 
    | (LBind (vs,_) as i)::lc' -> 
      let s = List.fold_left (fun s v -> Me.remove (mk_V v) s) s vs in
      aux s (i::rc) lc'
    | LSamp(v,d)::lc' ->
      let d = norm_distr ~norm:nf s d in
      let s = Me.remove (mk_V v) s in
      aux s (LSamp(v,d)::rc) lc'
    | LGuard e::lc' ->
      aux s (LGuard (nf (e_subst s e)) :: rc) lc' in
  aux s [] lc
    
let norm_gdef ?norm:(nf=norm_expr_def) g =
  let rec aux s rc lc = 
    match lc with
    | [] -> List.rev rc, s
    | GLet(v,e) :: lc' ->
      let e = nf (e_subst s e) in
      let v = mk_V v in
      let s = Me.add v e s in
      aux s rc lc'
    | GSamp(v, d) :: lc' ->
      let d = norm_distr ~norm:nf s d in
      let s = Me.remove (mk_V v) s in
      aux s (GSamp(v,d) :: rc) lc'
    | GCall(vs, e, odefs) :: lc'->
      let e = nf (e_subst s e) in
      let odefs = List.map (norm_odef ~norm:nf s) odefs in
      let s = List.fold_left (fun s v -> Me.remove (mk_V v) s) s vs in
      aux s (GCall(vs, e, odefs)::rc) lc'
  in
  aux Me.empty [] g

let norm_ju ?norm:(nf=norm_expr_def) ju =
  let g,s = norm_gdef ~norm:nf ju.ju_gdef in
  { ju_gdef = g;
    ju_ev = nf (e_subst s ju.ju_ev) }

(* unfold all lets and norm *)
let rnorm ju = [ norm_ju ju ]

(* norm without unfolding *)
let rnorm_nounfold ju = [ map_ju_exp norm_expr_def ju ]

(* norm without unfolding *)
let runfold_only ju = [ norm_ju ~norm:(fun x -> x) ju ]

(* Swapping instruction *)

let disjoint s1 s2 = 
  Se.is_empty (Se.inter s1 s2)

let check_swap read write i c =
  let i = [i] in
  let ir = read i in
  let iw = write i in
  let cr = read c in
  let cw = write c in
  if not (disjoint iw cw && 
            disjoint ir cw &&
            disjoint cr iw) then 
    failwith "swap : can not swap" (* FIXME improve the error message *)
    
let is_call = function
  | GCall _ -> true
  | _ -> false

let has_call c = List.exists is_call c

let swap i delta ju = 
  if delta = 0 then ju
  else
    let i,(hd,tl,e) = get_ju_ctxt ju i in
    let c1,c2,c3 = 
      if delta < 0 then 
        let hhd, thd = cut_n (-delta) hd in
        thd, hhd, tl
      else
        let htl, ttl = cut_n delta tl in
        hd, List.rev htl, ttl in
    check_swap read_gcmds write_gcmds i c2;
    if is_call i && has_call c2 then
      failwith "swap : can not swap";
    let c2,c3 = if delta > 0 then c2, i::c3 else i::c2, c3 in
    set_ju_ctxt c2 (c1,c3,e)

let rswap i delta ju = [swap i delta ju]

let swap_oracle i delta ju = 
  if delta = 0 then ju
  else
    let i,(((hd,tl), odecl, call), ctxt) = get_ju_octxt ju i in
    let c1,c2,c3 = 
      if delta < 0 then
        let hhd,thd = cut_n delta hd in
        thd,hhd,tl
      else 
        let htl, ttl = cut_n delta tl in
        hd, List.rev htl, ttl in
    check_swap read_lcmds write_lcmds i c2;
    let c2, c3 = 
      if delta > 0 then c2, i::c3 else i::c2, c3 in
    set_ju_octxt c2 (((c1,c3),odecl,call),ctxt)

let rswap_oracle i delta ju =
  [swap_oracle i delta ju]
  
  
  
