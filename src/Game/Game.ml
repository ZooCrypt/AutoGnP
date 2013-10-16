(* Games *)
open Util
open Type
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
          | LSamp  of Vsym.t * distr
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
          | GCall of Vsym.t list * Asym.t * Expr.expr * odef list
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

(*let pp_v fmt v = F.fprintf fmt "%a_%i" Vsym.pp v (Id.tag v.Vsym.id) *)
let pp_v fmt v = Vsym.pp fmt v 

let pp_binder fmt vs = match vs with
  | [v] -> pp_v fmt v
  | _   -> F.fprintf fmt "(%a)" (pp_list "," pp_v) vs

let pp_lcmd fmt lc = match lc with
  | LLet(vs,e)  -> F.fprintf fmt "let %a = %a" pp_binder [vs]
                     pp_exp e
  | LBind(vs,h) -> F.fprintf fmt "%a <- L_%a" pp_binder vs
                     Hsym.pp h
  | LSamp(v,d)  -> F.fprintf fmt "%a <-$ %a" pp_binder [v]
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
  | GSamp(v,d)      -> F.fprintf fmt "%a <-$ %a" pp_binder [v]
                         pp_distr d
  | GCall(vs,asym,e,[]) -> F.fprintf fmt "%a <- %a(%a)" pp_binder vs Asym.pp asym pp_exp_tnp e
  | GCall(vs,asym,e,os) -> F.fprintf fmt "%a <- %a(%a) with \n  %a"
                             pp_binder vs Asym.pp asym pp_exp_tnp e
                             (pp_list ",@\n" pp_odef) os

let pp_gdef fmt gd =
  F.fprintf fmt "@[%a @]" (pp_list ";\n" pp_gcmd) gd


let pp_ju fmt ju =
  F.fprintf fmt "@[%a\n : %a@]" pp_gdef ju.ju_gdef pp_exp ju.ju_ev

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
  | GCall(vs,asym,e,os) -> GCall(vs, asym, f e, List.map (map_odef_exp f) os)

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
  | GCall(_,_,e,os) -> f e; List.iter (iter_odef_exp f) os

let iter_gdef_exp f gdef = List.iter (iter_gcmd_exp f) gdef

let iter_ju_exp f ju =
  iter_gdef_exp f ju.ju_gdef; f ju.ju_ev


(* ----------------------------------------------------------------------- *)
(** {4 Read and write variables } *)

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
  | GCall(_,_,e,odef) -> 
    Se.union (e_vars e) (fold_union read_odef odef)

let read_gcmds c = fold_union read_gcmd c

let write_gcmd = function
  | GLet (x,_) | GSamp (x,_) -> Se.singleton (mk_V x)
  | GCall (xs,_,_,_) -> add_binding xs

let write_gcmds c = fold_union write_gcmd c

let has_log_distr (_,es) = List.exists has_log es
  
let has_log_lcmd = function
  | LLet(_,e) | LGuard e -> has_log e
  | LBind _ -> false
  | LSamp(_,d) -> has_log_distr d

let has_log_lcmds c = List.exists has_log_lcmd c

let has_log_o (_,_,c,e) = has_log e || has_log_lcmds c

let has_log_gcmd = function
  | GLet(_,e) -> has_log e
  | GSamp(_,d) -> has_log_distr d
  | GCall(_,_,e,os) ->
    has_log e || List.exists has_log_o os 

let has_log_gcmds c = List.exists has_log_gcmd c

(* ----------------------------------------------------------------------- *)
(** {5 Helper functions for rules } *)

(** smart constructors *)
let is_call = function
  | GCall _ -> true
  | _ -> false

let has_call c = List.exists is_call c


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
  | GCall(_,_,_,os) ->
      let (o,vs,ms,e) = List.nth os j in
      o,vs,split_n k ms, e
  | _ -> assert false

let get_ju_octxt ju (i,j,k) = 
  match get_ju_ctxt ju i with
  | GCall(vsa,asym,e,os), ctxt ->
    let rohd, (o,vs,ms,oe), otl = split_n j os in
    let rhd, i, tl = split_n k ms in
    i, (((rhd,tl), (o,vs,oe), (rohd, otl, (asym,vsa,e))), ctxt)
  | _ -> assert false

let set_ju_octxt cmd (((rhd,tl), (o,vs,oe), (rohd, otl, (asym,vsa,e))), ctxt) =
  let ms = List.rev_append rhd (cmd @ tl) in
  let os = List.rev_append rohd ((o,vs,ms, oe) :: otl) in
  let i = [GCall(vsa, asym, e, os)] in
  set_ju_ctxt i ctxt

let set_ju_lcmd ju p cmds = 
  let _, ctxt = get_ju_octxt ju p in
  set_ju_octxt cmds ctxt


(* ----------------------------------------------------------------------- *)
(** {6 Equality} *) 

let d_equal (ty1,es1) (ty2,es2) = 
  ty_equal ty1 ty2 && 
    list_eq_for_all2 e_equal es1 es2
  
let lc_equal i1 i2 = 
  match i1, i2 with
  | LLet(x1,e1), LLet(x2,e2) ->
    Vsym.equal x1 x2 && e_equal e1 e2
  | LBind(xs1,h1), LBind(xs2,h2) ->
    list_eq_for_all2 Vsym.equal xs1 xs2 && Hsym.equal h1 h2
  | LSamp(x1,d1), LSamp(x2,d2) ->
    Vsym.equal x1 x2 && d_equal d1 d2
  | LGuard e1, LGuard e2 -> e_equal e1 e2
  | LLet _  , (LBind _ | LSamp _ | LGuard _) 
  | LBind _ , (LLet _  | LSamp _ | LGuard _) 
  | LSamp _ , (LLet _  | LBind _ | LGuard _) 
  | LGuard _, (LLet _  | LBind _ | LSamp _ ) -> false

let lcs_equal c1 c2 = list_eq_for_all2 lc_equal c1 c2

let o_equal (o1,xs1,c1,e1) (o2,xs2,c2,e2) = 
  Osym.equal o1 o2 &&
    list_eq_for_all2 Vsym.equal xs1 xs2 &&
    lcs_equal c1 c2 &&
    e_equal e1 e2 

let gc_equal i1 i2 =
  match i1, i2 with
  | GLet(x1,e1), GLet(x2,e2) ->
    Vsym.equal x1 x2 && e_equal e1 e2
  | GSamp(x1,d1), GSamp(x2,d2) ->
    Vsym.equal x1 x2 && d_equal d1 d2
  | GCall(xs1,as1,e1,os1), GCall(xs2,as2,e2,os2) ->
    list_eq_for_all2 Vsym.equal xs1 xs2 &&
      e_equal e1 e2 &&
      list_eq_for_all2 o_equal os1 os2 &&
      Asym.equal as1 as2
  | GLet _, (GSamp _ | GCall _) 
  | GSamp _, (GLet _ | GCall _) 
  | GCall _, (GLet _ | GSamp _) -> false

let gcs_equal c1 c2 = list_eq_for_all2 gc_equal c1 c2

let ju_equal ju1 ju2 = 
  gcs_equal ju1.ju_gdef ju2.ju_gdef &&
    e_equal ju1.ju_ev ju2.ju_ev


(* ----------------------------------------------------------------------- *)
(** {7 Normalization } *) 

let norm_expr_def e = Norm.abbrev_ggen (Norm.norm_expr e)

let norm_distr ?norm:(nf=Norm.norm_expr) s (ty,es) = 
  (ty, List.map (fun e -> nf (e_subst s e)) es)

let norm_odef ?norm:(nf=Norm.norm_expr) s (o,vs,lc,e) =
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
    
let norm_gdef ?norm:(nf=Norm.norm_expr) g =
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
    | GCall(vs, asym, e, odefs) :: lc'->
      let e = nf (e_subst s e) in
      let odefs = List.map (norm_odef ~norm:nf s) odefs in
      let s = List.fold_left (fun s v -> Me.remove (mk_V v) s) s vs in
      aux s (GCall(vs, asym, e, odefs)::rc) lc'
  in
  aux Me.empty [] g

let norm_ju ?norm:(nf=Norm.norm_expr) ju =
  let g,s = norm_gdef ~norm:nf ju.ju_gdef in
  { ju_gdef = g;
    ju_ev = nf (e_subst s ju.ju_ev) }

  
