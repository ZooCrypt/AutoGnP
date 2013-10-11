(* Representing Games *)

open Type
open Util
open Expr

module F = Format
(* ----------------------------------------------------------------------- *)
(** {1 Types} *)


(* (excepted) distributions for sampling *)
type distr = Type.ty * Expr.expr list (* uniform distribution over type t except for given values *)

(* list monad command for oracle definition *)
type lcmd = LLet   of Vsym.t * Expr.expr       (* LLet(x,e): let (x1,..,xk) = e *)
          | LBind  of Vsym.t list * Hsym.t     (* LBind([x1;..;xk], h): (x1,..,xk) <- L_h *)
          | LSamp  of Vsym.t * distr           (* LSamp(x,d): x <-$ d *)
          | LGuard of Expr.expr                (* LGuard(t): t *)

(* oracle definition *)
type odef = Osym.t * Vsym.t list * lcmd list * Expr.expr
  (* (o,[x1;..;xl], [m1;..;mk],e): o(x1,..,xl) = [e | m1, .., mk] *)

(* game command *)
type gcmd = GLet  of Vsym.t * Expr.expr                    (* GLet([x1;..xk], e): let (x1,..,xk) = e *)
          | GSamp of Vsym.t * distr                        (* GSamp(x,d): x <-$ d *)
          | GCall of Vsym.t list * Expr.expr * odef list

(* game definition *)
type gdef = gcmd list

let map_distr_exp f (t,es) = (t, List.map f es)

let map_lcmd_exp f lcmd =
  match lcmd with
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

let norm_subst_ggen s e = Norm.norm_ggen (Norm.norm_subst s e)

let norm_distr s (ty,es) = 
  (ty, List.map (norm_subst_ggen s) es)

let norm_orcl s (o,vs,lc,e) =
  let rec aux s rc lc = 
    match lc with
    | [] -> (o,vs,List.rev rc, norm_subst_ggen s e)
    | LLet (v, e) :: lc' ->
      let e = Norm.norm_subst s e in
      let v = mk_V v in
      let s = Me.add v e s in
      aux s rc lc' 
    | (LBind _ as i)::lc' -> aux s (i::rc) lc'
    | LSamp(v,d)::lc' ->
      aux s (LSamp(v,norm_distr s d)::rc) lc'
    | LGuard e::lc' ->
      aux s (LGuard (norm_subst_ggen s e) :: rc) lc' in
  aux s [] lc
    
let norm_game g =
  let rec aux s rc lc = 
    match lc with
  | [] -> List.rev rc
  | GLet(v,e) :: lc' ->
    let e = Norm.norm_subst s e in
    let v = mk_V v in
    let s = Me.add v e s in
    aux s rc lc'
  | GSamp(v, d) :: lc' ->
    aux s (GSamp(v,norm_distr s d) :: rc) lc'
  | GCall(vs, e, odefs) :: lc'->
    let e = Norm.norm_ggen (Norm.norm_subst s e) in
    let odefs = List.map (norm_orcl s) odefs in
    aux s (GCall(vs, e, odefs)::rc) lc' in
  aux Me.empty [] g


(* ----------------------------------------------------------------------- *)
(** {2 Well-formedness} *)

let wf_odef _od = true

let wf_gdef _gd = true

(* ----------------------------------------------------------------------- *)
(** {3 Pretty printing} *)

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
