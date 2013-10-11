(* Representing Games *)

open Type
open Util
open Expr
open Norm

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
  | [] -> List.rev rc, s
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
(** {3 Judgments and rules } *)

let apply rule goals = match goals with
  | g::gs -> rule g @ gs
  | _ -> failwith "there are no goals"

let delay goals = match goals with
  | g::gs -> gs@[g]
  | []    -> []

type ev = expr

type judgment = { ju_gdef : gdef; ju_ev : ev }

let mk_ju gd ev = { ju_gdef = gd; ju_ev = ev }

let rnorm ju =
  let g,s = norm_game ju.ju_gdef in
  [{ ju_gdef = g;
    ju_ev = norm_subst_ggen s ju.ju_ev }]

let map_ju_exp f ju =
  { ju_gdef = map_gdef_exp f ju.ju_gdef; ju_ev = f ju.ju_ev }

type ju_zipper =
  { juz_pos : int;
    juz_left : gcmd list;
    juz_foc : gcmd;
    juz_right : gcmd list;
    juz_ev : ev }

let mk_juz ju = match ju.ju_gdef with
  | []    -> failwith "Cannot create zipper for empty game definition"
  | c::cs -> { juz_pos = 0;
               juz_left = [];
               juz_foc = c;
               juz_right = cs;
               juz_ev = ju.ju_ev }

let ju_of_juz z =
  {ju_gdef = List.rev z.juz_left@[z.juz_foc]@z.juz_right; ju_ev = z.juz_ev }

let juz_right z = match z.juz_right with
  | []    -> failwith "Cannot move right, focused on last command"
  | c::cs -> {z with juz_pos = z.juz_pos +1;
                     juz_left = z.juz_foc::z.juz_left;
                     juz_foc = c;
                     juz_right = cs }

(* let juz_left (p, left, foc, right, ev) = match left with
  | []    -> failwith "Cannot move left, focused on first command"
  | c::cs -> (p+1, cs, c, foc::right, ev)
 *)
let juz_at i0 ju0 =
  assert (i0 >= 0);
  let juz0 = mk_juz ju0 in
  let rec go i juz = if i = 0 then juz else go (i-1) (juz_right juz) in
  go i0 juz0

type context = (Vsym.t * expr)

let inst_ctxt (v, e') e = e_replace (mk_V v) e e' 

let e_equalmod e e' = e_equal (norm_expr e) (norm_expr e')

(* 'random p c1 c2' takes a position p and two contexts. It first
   ensures that there is a random sampling 'x <-$ d' at position p.
   For now, its not excepted. Otherwise we have to apply c1/c2 to
   the excepted values.
   Then it checks that under the inequalities that hold at position p,
   forall x in supp(d), c2(c1(x)) = x.  *)
let random p c1 c2 ju =
  let z = juz_at p ju in
  match z.juz_foc with
  | GSamp(vs,((t,[]) as d) ) ->
    let v = mk_V vs in
    if e_equalmod (inst_ctxt c2 (inst_ctxt c1 v)) v &&
       e_equalmod (inst_ctxt c1 (inst_ctxt c2 v)) v
    then (
      let freshv = Vsym.mk (Id.name vs.Vsym.id) t in
      let z = { z with
                juz_foc   = GSamp(freshv,d);
                juz_right = GLet(vs, inst_ctxt c1 (mk_V freshv))::z.juz_right }
      in [ ju_of_juz z ]
    ) else (
      failwith "random: contexts not bijective"
    )
  | _ -> failwith "random: position given is not a sampling"

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


let pp_ju fmt ju =
  F.fprintf fmt "@[%a@. : %a@]" pp_gdef ju.ju_gdef pp_exp ju.ju_ev

let pp_ps fmt ps =
  let ju_idxs =
    let i = ref 0 in List.map (fun ps -> incr i; (!i, ps)) ps
  in
  let pp_ju_idx fmt (i,ju) = F.fprintf fmt "@[%i.@[ %a @]" i pp_ju ju in
  F.fprintf fmt "%a\n--------------------\n\n"
    (pp_list "\n\n" pp_ju_idx) ju_idxs


