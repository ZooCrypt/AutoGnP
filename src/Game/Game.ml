(** Cryptographic game definitions. *)

(*i*)
open Abbrevs
open Util
open Type
open Expr
open ExprUtils
open Syms
open Norm
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Types} *)

(** Variable, adversary, oracle, and hash symbol. *)
type vs  = Vsym.t
type ads = Asym.t
type os  = Osym.t
type hs  = Hsym.t
type ors = Oracle.t

(** (Excepted) Distributions for sampling. *)
type distr = ty * expr list  (*r uniform distribution over type $t$ except for given values *)

(** List monad command for oracle definition. *)
type lcmd =
  | LLet   of vs * expr    (*r $LLet(\vec{x},e): \text{let }(x_1,..,x_k) = e$ *)
  | LBind  of vs list * hs (*r $LBind(\vec{x}, h): (x_1,..,x_k) \leftarrow L_h$ *)
  | LSamp  of vs * distr   (*r $LSamp(x,d): x \leftarrow_{\$} d$ *)
  | LGuard of expr         (*r $LGuard(t): t$ *)

type obody = lcmd list * Expr.expr

type ohybrid = { odef_less : obody; odef_eq : obody; odef_greater : obody }

type odecl =
  | Odef of obody
  | Ohybrid of ohybrid

let is_hybrid = function Odef _ -> false | Ohybrid _ -> true

type ohtype = OHless | OHeq | OHgreater
type otype = Onohyb | Ohyb of ohtype

(** Oracle definition. *)
type odef = os * vs list * odecl (*r
  $(o,\vec{x}, \vec{m},e): o(x_1,..,x_l) = [e | m_1, .., m_k]$ *)

(** Game command. *)
type gcmd =
  | GLet    of vs * expr (*r $GLet(\vec{x},e): let (x_1,..,x_k) = e$ *)
  | GAssert of expr      (*r $GAssert(e): assert (e)$ *)
  | GSamp   of vs * distr (*r $GSamp(x,d): x \leftarrow_{\$} d$ *)
  | GCall   of vs list * ads * expr * odef list (*r
      $GCall(\vec{x}, e, \vec{o}): (x_1,..,x_k) \leftarrow A(e) \text{ with }o_1,..,o_l$ *)

(** Game definition. *)
type gdef = gcmd list

(** An event is just a quantified expression. *)
type quant = EvForall | EvExists
type ev = { ev_quant: quant; ev_binding: (vs list * ors) list; ev_expr:expr }

(** A security experiment consists of a game and an event. *)
type sec_exp = { se_gdef : gdef; se_ev : ev }

(*i*)
(* ----------------------------------------------------------------------- *)
(* \hd{Pretty printing} *)

let pp_distr ~qual fmt (ty,es) = 
  match es with
  | [] -> pp_ty fmt ty
  | _  -> F.fprintf fmt "@[<hov 2>%a \\ {@[<hov 0>%a}@]@]" pp_ty ty
            (pp_list "," (pp_exp_qual ~qual)) es

(* let pp_v fmt v = F.fprintf fmt "%a_%i" Vsym.pp v (Id.tag v.Vsym.id) *)
let pp_v fmt v = Vsym.pp fmt v 

let pp_binder ~qual fmt vs = match vs with
  | [v] -> Vsym.pp_qual ~qual fmt v
  | _   -> F.fprintf fmt "(@[<hov 0>%a@])" (pp_list "," (Vsym.pp_qual ~qual)) vs

let pp_lcmd ~qual fmt lc = 
  match lc with
  | LLet(vs,e)  -> 
    F.fprintf fmt "@[<hov 2>let %a =@ %a@]"
      (pp_binder ~qual) [vs]
      (pp_exp_qual ~qual) e
  | LBind(vs,h) -> 
    F.fprintf fmt "@[<hov 2>%a <-@ L_%a@]" (pp_binder ~qual) vs Hsym.pp h
  | LSamp(v,d)  -> 
    F.fprintf fmt "@[<hov 2>%a <-$@ %a@]"
      (pp_binder ~qual) [v]
      (pp_distr ~qual) d
  | LGuard(e)   -> pp_exp_qual ~qual fmt e

let pp_ilcmd ~nonum ~qual fmt (i,lc) =
  if nonum
  then (pp_lcmd ~qual fmt) lc
  else F.fprintf fmt "%i: %a" i (pp_lcmd ~qual) lc

let pp_lcomp ~nonum ~qual fmt (e,m) =
  match m with
  | [] ->
    F.fprintf fmt "%sreturn %a"
      (if nonum then "" else "1: ")
      (pp_exp_qual ~qual) e
      
  | _  ->
    F.fprintf fmt "@[%a;@\n%sreturn %a@]"
      (pp_list ";@\n" (pp_ilcmd ~nonum ~qual))
      (num_list m)
      (if nonum then "" else F.sprintf "%i: " (L.length m + 1))
      (pp_exp_qual ~qual) e

let string_of_otype = function
  | OHless    -> "<"
  | OHeq      -> "="
  | OHgreater -> ">"

let pp_ohtype fmt oht = pp_string fmt (string_of_otype oht)

let pp_otype fmt ot =
  match ot with
  | Onohyb   -> pp_string fmt "no hybrid"
  | Ohyb oht -> pp_ohtype fmt oht

let pp_obody ~nonum osym ootype fmt (ms,e) =
  F.fprintf fmt "{ %s@\n  @[<v>%a@] }"
    (match ootype with None -> "" | Some ot -> "(* "^string_of_otype ot^" *)")
    (pp_lcomp ~nonum ~qual:(Qual osym)) (e,ms)

let pp_ohybrid ~nonum osym fmt oh =
  F.fprintf fmt "[@\n  @[<v>%a@]@\n  @[<v>%a@]@\n  @[<v>%a@]@\n]"
    (pp_obody ~nonum osym (Some OHless))    oh.odef_less
    (pp_obody ~nonum osym (Some OHeq))      oh.odef_eq
    (pp_obody ~nonum osym (Some OHgreater)) oh.odef_greater

let pp_odecl ~nonum osym fmt od =
  match od with
  | Odef od    -> pp_obody ~nonum osym None fmt od
  | Ohybrid oh -> pp_ohybrid ~nonum osym fmt oh

let pp_odef ~nonum fmt (o, vs, od) =
  F.fprintf fmt "@[<v>%a(@[<hov 0>%a@]) = %a@]" 
    Osym.pp o
    (pp_list "," (Vsym.pp_qual ~qual:(Qual o))) vs
    (pp_odecl ~nonum o) od

let pp_gcmd ~nonum fmt gc = match gc with
  | GLet(vs,e) -> 
    F.fprintf fmt "@[<hov 2>let %a =@ %a@]" (pp_binder ~qual:Unqual) [vs] pp_exp e
  | GAssert(e) -> 
    F.fprintf fmt "@[<hov 2>assert(%a)@]" pp_exp e
  | GSamp(v,d) -> 
    F.fprintf fmt "@[<hov 2>%a <-$@ %a@]"
      (pp_binder ~qual:Unqual) [v]
      (pp_distr ~qual:Unqual) d
  | GCall(vs,asym,e,[]) -> 
    F.fprintf fmt "@[<hov 2>%a <-@ %a(@[%a@])@]" 
      (pp_binder ~qual:Unqual) vs Asym.pp asym pp_exp_tnp e 
  | GCall(vs,asym,e,od) -> 
    F.fprintf fmt "@[<hov 2>%a <-@ %a(@[%a@]) with@\n%a@]"
      (pp_binder ~qual:Unqual) vs Asym.pp asym 
      pp_exp_tnp e
      (pp_list ",@;" (pp_odef ~nonum)) od

let pp_igcmd fmt (i,gc) = 
  F.fprintf fmt "@[%i: %a@]" i (pp_gcmd ~nonum:false) gc 

let pp_gdef ~nonum fmt gd =
  if nonum then
    pp_list ";@;" (pp_gcmd ~nonum) fmt gd
  else
    pp_list ";@;" pp_igcmd fmt (num_list gd)

let pp_quant fmt = function
  | EvForall -> F.fprintf fmt "forall"
  | EvExists -> F.fprintf fmt "exists"

let pp_binding1 fmt (vs,ors) = 
  let pp_bdecl fmt vs = 
    match vs with
    | [v] -> Vsym.pp fmt v
    | _   -> F.fprintf fmt "(%a)" (pp_list "," Vsym.pp) vs in
  F.fprintf fmt "%a in L_%a"
            pp_bdecl vs Oracle.pp ors

let pp_binding = pp_list ", " pp_binding1 

let pp_ev fmt ev = 
  if ev.ev_binding = [] then pp_exp fmt ev.ev_expr 
  else
    F.fprintf fmt "@[<hov>%a (%a):@ %a@]"
      pp_quant ev.ev_quant
      pp_binding ev.ev_binding
      pp_exp ev.ev_expr

let pp_se fmt se =
  F.fprintf fmt "@[<v 0>%a;@,: %a@]" (pp_gdef ~nonum:false) se.se_gdef
    pp_ev se.se_ev


let pp_se_nonum fmt se =
  F.fprintf fmt "@[<v 0>%a;@,: %a@]" (pp_gdef ~nonum:true) se.se_gdef 
    pp_ev se.se_ev

let pp_ps fmt ps =
  let se_idxs =
    let i = ref 0 in L.map (fun ps -> incr i; (!i, ps)) ps
  in
  let pp_se_idx fmt (i,se) = F.fprintf fmt "@[%i.@[ %a @]@]" i pp_se se in
  F.fprintf fmt "%a\n--------------------\n\n"
    (pp_list "\n\n" pp_se_idx) se_idxs

(*i*)


(*i ----------------------------------------------------------------------- i*)
(* \hd{Generic functions: [map_*_expr] and [iter_*_expr]} *)

(** map *)
let map_distr_exp f (t,es) = (t, L.map f es)

let map_lcmd_exp f lcmd = match lcmd with
  | LLet(vs,e)  -> LLet(vs, f e)
  | LBind(vs,h) -> LBind(vs,h)
  | LSamp(v,d)  -> LSamp(v, map_distr_exp f d)
  | LGuard(e)   -> LGuard(f e)


let map_ohybrid f { odef_less; odef_eq; odef_greater } =
  { odef_less = f odef_less;
    odef_eq = f odef_eq;
    odef_greater = f odef_greater }

let map_obody_exp f (ms,e) =
  L.map (map_lcmd_exp f) ms, f e

let map_odecl_exp f od =
  match od with
  | Odef od    -> Odef    (map_obody_exp f od)
  | Ohybrid oh -> Ohybrid (map_ohybrid (map_obody_exp f) oh)

let map_odef_exp f (o,vs,od) =
  (o,vs,map_odecl_exp f od)


let map_gcmd_exp f gcmd = match gcmd with
  | GLet(vs,e)          -> GLet(vs, f e)
  | GAssert(e)          -> GAssert(f e)
  | GSamp(v,d)          -> GSamp(v, map_distr_exp f d)
  | GCall(vs,asym,e,os) -> GCall(vs, asym, f e, L.map (map_odef_exp f) os)

let map_gdef_exp f gdef = L.map (map_gcmd_exp f) gdef

let map_ev_exp f ev = { ev with ev_expr = f ev.ev_expr }

let map_se_exp f se =
  { se_gdef = map_gdef_exp f se.se_gdef; se_ev = map_ev_exp f se.se_ev }

(** iter *)

let iter_distr_exp ?iexc:(iexc=false) f (_,es) = if iexc then L.iter f es

let iter_lcmd_exp ?iexc:(iexc=false) f lcmd = match lcmd with
  | LLet(_,e)  -> f e
  | LBind(_)   -> ()
  | LSamp(_,d) -> iter_distr_exp ~iexc f d
  | LGuard(e)  -> f e

let iter_obody_exp ?iexc:(iexc=false) f (ms,e) =
  L.iter (iter_lcmd_exp ~iexc f) ms; f e

let iter_ohybrid_exp ?iexc:(iexc=false) f { odef_less; odef_eq; odef_greater} =
  iter_obody_exp ~iexc f odef_less;
  iter_obody_exp ~iexc f odef_eq;
  iter_obody_exp ~iexc f odef_greater

let iter_odecl_exp ?iexc:(iexc=false) f od =
  match od with
  | Odef od    -> iter_obody_exp ~iexc f od
  | Ohybrid oh -> iter_ohybrid_exp ~iexc f oh

let iter_odef_exp ?iexc:(iexc=false) f (_o,_vs,od) =
  iter_odecl_exp ~iexc f od

let iter_gcmd_exp ?iexc:(iexc=false) f gcmd =
  match gcmd with
  | GLet(_,e)       -> f e
  | GAssert(e)      -> f e
  | GSamp(_,d)      -> iter_distr_exp ~iexc f d
  | GCall(_,_,e,od) -> f e; L.iter (iter_odef_exp ~iexc f) od

let iter_gcmd_exp_orcl ?iexc:(iexc=false) f gcmd = match gcmd with
  | GLet(_,_)     -> ()
  | GAssert(_)    -> ()
  | GSamp(_,_)    -> ()
  | GCall(_,_,_,od) -> L.iter (iter_odef_exp ~iexc f) od

let iter_gcmd_exp_no_orcl ?iexc:(iexc=false) f gcmd = match gcmd with
  | GLet(_,e)     -> f e
  | GAssert(e)    -> f e
  | GSamp(_,d)    -> iter_distr_exp ~iexc f d
  | GCall(_,_,e,_) -> f e

let iter_gdef_exp ?iexc:(iexc=false) f gdef =
  L.iter (iter_gcmd_exp_no_orcl ~iexc f) gdef;
  L.iter (iter_gcmd_exp_orcl ~iexc f) gdef

let iter_se_exp ?iexc:(iexc=false) f se =
  iter_gdef_exp ~iexc f se.se_gdef; f se.se_ev.ev_expr

(*i ----------------------------------------------------------------------- i*)
(* \hd{Positions and replacement functions} *)

type gcmd_pos = int

type odef_pos = (int * int)

type ocmd_pos = (int * int * int * otype)

type ocmd_pos_eq = (int * int * int)

let get_se_gcmd se p = L.nth se.se_gdef p

type se_ctxt = {
  sec_left : gdef;
  sec_right : gdef;
  sec_ev : ev
}
  
let get_se_ctxt_len se ~pos ~len =
  let rhd,tl =  cut_n pos se.se_gdef in
  let cmds, cright = cut_n len tl in
  L.rev cmds, { sec_left = rhd; sec_right = cright; sec_ev = se.se_ev}

let get_se_ctxt se pos =
  match get_se_ctxt_len se ~pos ~len:1 with
  | [cmd], ctxt ->
    cmd, ctxt
  | _ -> assert false

let set_se_ctxt cmds {sec_left; sec_right; sec_ev} =
  { se_gdef = L.rev_append sec_left (cmds @ sec_right);
    se_ev   = sec_ev }

let set_se_gcmd se pos cmds =
  assert (pos >= 0 && pos < L.length se.se_gdef);
  let _, ctxt = get_se_ctxt se pos in
  set_se_ctxt cmds ctxt

let get_obody od otype =
  match otype, od with
  | Onohyb,         Odef ob    -> ob
  | Ohyb OHless,    Ohybrid oh -> oh.odef_less
  | Ohyb OHeq,      Ohybrid oh -> oh.odef_eq
  | Ohyb OHgreater, Ohybrid oh -> oh.odef_greater
  | _ -> assert false

let get_se_lcmd se (i,j,k,otype) = 
  match get_se_gcmd se i with
  | GCall(_,_,_,ods) ->
    let (o,vs,od) = L.nth ods j in
    let (ms,e) = get_obody od otype in
    o,vs,split_n k ms, e
  | _ -> assert false

type se_octxt = {
  seoc_asym : ads;
  seoc_avars : vs list;
  seoc_aarg : expr;
  seoc_oleft : odef list;
  seoc_oright : odef list;
  seoc_obless : obody option;
  seoc_obeq : obody option;
  seoc_obgreater : obody option;
  seoc_osym : os;
  seoc_oargs: vs list;
  seoc_return : expr;
  seoc_cleft : lcmd list;
  seoc_cright : lcmd list;
  seoc_sec : se_ctxt
}

let get_se_octxt_len se (i,j,k,ootype) len = 
  match get_se_ctxt se i with
  | GCall(vsa,asym,e,os), sec ->
    let rohd, (o,vs,od), otl = split_n j os in
    let (ms,oe) = get_obody od ootype in
    let rhd, tl = cut_n (min k (List.length ms)) ms in
    let cmds,cright = cut_n len tl in
    let obless = match ootype with
      | Ohyb (OHeq |  OHgreater) -> Some (get_obody od (Ohyb OHless))
      | _ -> None
    in
    let obeq = match ootype with
      | Ohyb (OHless | OHgreater) -> Some (get_obody od (Ohyb OHeq))
      | _ -> None
    in
    let obgreater = match ootype with
      | Ohyb (OHless | OHeq) -> Some (get_obody od (Ohyb OHgreater))
      | _ -> None
    in
    let ctx =
      { seoc_asym = asym;
        seoc_avars = vsa;
        seoc_aarg = e;
        seoc_oright = rohd;
        seoc_oleft = otl;
        seoc_obless = obless;
        seoc_obeq = obeq;
        seoc_obgreater = obgreater;
        seoc_osym = o;
        seoc_oargs = vs;
        seoc_return = oe;
        seoc_cleft = rhd;
        seoc_cright = cright;
        seoc_sec = sec }
    in
    L.rev cmds, ctx
  | _ -> assert false

let set_se_octxt lcmds c =
  let ms = L.rev_append c.seoc_cleft (lcmds@c.seoc_cright) in
  let ob = (ms,c.seoc_return) in
  let odecl =
    match c.seoc_obless, c.seoc_obeq,  c.seoc_obgreater with
    | None,    None,     None   -> Odef ob
    | None,    Some oe, Some og -> Ohybrid { odef_less = ob; odef_eq = oe; odef_greater = og }
    | Some ol, None,    Some og -> Ohybrid { odef_less = ol; odef_eq = ob; odef_greater = og }
    | Some ol, Some oe, None    -> Ohybrid { odef_less = ol; odef_eq = oe; odef_greater = ob }
    | _ -> assert false
  in 
  let odef = (c.seoc_osym,c.seoc_oargs,odecl) in
  let os = L.rev_append c.seoc_oleft (odef :: c.seoc_oright) in
  let i = [GCall(c.seoc_avars, c.seoc_asym, c.seoc_aarg, os)] in
  set_se_ctxt i c.seoc_sec

let get_se_octxt se p = 
  match get_se_octxt_len se p 1 with
  | [cmd], ctxt -> cmd, ctxt
  | _           -> assert false

let set_se_lcmd se p cmds = 
  let _, ctxt = get_se_octxt se p in
  set_se_octxt cmds ctxt

(*i ----------------------------------------------------------------------- i*)
(* \hd{Iterate with context} *)

type iter_pos =
  | InEv
  | InMain       of gcmd_pos
  | InOrclReturn of ocmd_pos * ty * ty
  | InOrcl       of ocmd_pos * ty * ty
    (* position, adversary argument type, oracle type *)

let pp_iter_pos fmt ip =
  match ip with
  | InEv                                  -> F.fprintf fmt "inEv"
  | InMain(i)                             -> F.fprintf fmt "inMain(%i)" i
  | InOrcl((gpos,o_idx,opos,otype),_,_)  -> 
    F.fprintf fmt "inOrcl(%i,%i,%i,%a)" gpos o_idx opos pp_otype otype
  | InOrclReturn((gpos,o_idx,_,_),_,_) -> F.fprintf fmt "inOreturn(%i,%i)" gpos o_idx

type iter_ctx = {
  ic_pos     : iter_pos;
  ic_isZero  : expr list;
  ic_nonZero : expr list
}

let empty_iter_ctx pos = {
  ic_pos     = pos;
  ic_isZero  = [];
  ic_nonZero = []
}

let pp_iter_ctx fmt ic =
  F.fprintf fmt "pos: %a, isZero: %a, nonZero: %a"
    pp_iter_pos ic.ic_pos
    (pp_list " /\\ " (pp_around "" " = 0" pp_exp)) ic.ic_isZero
    (pp_list " /\\ " (pp_around "" " <> 0" pp_exp)) ic.ic_nonZero

let iter_ctx_obody_exp argtype gpos o_idx nz ?iexc:(iexc=false) f o ootype (ms,e) =
  let tests = ref 0 in
  let nonZero = ref nz in
  let isZero  = ref [] in
  let go _lcmd_idx lcmd =
    let ctx = { (empty_iter_ctx (InOrcl((gpos,o_idx,!tests,ootype),argtype,o.Osym.dom)))
                  with ic_nonZero = !nonZero; ic_isZero = !isZero }
    in
    match lcmd with
    | LLet(_,e) ->
      f ctx e
    | LBind(_) ->
      ()
    | LSamp(v,(_,es)) ->
      if iexc then L.iter (f ctx) es;
      let ve = mk_V v in
      let neqs = L.map (fun e -> destr_Eq_norm (mk_Eq ve e)) es in
      nonZero := catSome neqs @ !nonZero
    | LGuard(e)  ->
      incr tests;
      f ctx e;
      isZero := (catSome (L.map destr_Eq_norm [e])) @ !isZero;
      nonZero := (catSome (L.map destr_Eq_norm [e])) @ !nonZero
  in
  L.iteri go ms;
  let ctx = { ic_pos = InOrclReturn((gpos,o_idx,!tests,ootype),argtype,o.Osym.dom);
              ic_nonZero = !nonZero; ic_isZero = !isZero }
  in
  f ctx e

let iter_ctx_odecl_exp argtype gpos o_idx nz ?iexc:(iexc=false) f os od =
  match od with
  | Odef ob -> iter_ctx_obody_exp argtype gpos o_idx nz ~iexc f os Onohyb ob
  | Ohybrid oh ->
    iter_ctx_obody_exp argtype gpos o_idx nz ~iexc f os (Ohyb OHless) oh.odef_less;
    iter_ctx_obody_exp argtype gpos o_idx nz ~iexc f os (Ohyb OHeq) oh.odef_eq;
    iter_ctx_obody_exp argtype gpos o_idx nz ~iexc f os (Ohyb OHgreater) oh.odef_greater

let iter_ctx_odef_exp argtype gpos o_idx nz ?iexc:(iexc=false) f (os,_vs,od) =
  iter_ctx_odecl_exp argtype gpos o_idx nz ~iexc f os od

let iter_ctx_gdef_exp ?iexc:(iexc=false) f gdef =
  let nonZero = ref [] in
  let go pos gcmd =
    let ctx = { ic_pos = InMain(pos); ic_isZero = []; ic_nonZero = !nonZero } in
    match gcmd with
    | GLet(_,e) ->
      f ctx e
    | GAssert(e) ->
      f ctx e
    | GCall(_,_,e,ods) ->
      f ctx e;
      L.iteri
        (fun oi -> iter_ctx_odef_exp e.e_ty pos oi !nonZero ~iexc f)
        ods
    | GSamp(v,(_,es)) ->
      if iexc then L.iter (f ctx) es;
      let ve = mk_V v in
      let neqs = L.map (fun e -> destr_Eq_norm (mk_Eq ve e)) es in
      nonZero := catSome neqs @ !nonZero
  in
  L.iteri go gdef;
  !nonZero

let iter_ctx_se_exp ?iexc:(iexc=false) f se =
  let nz = iter_ctx_gdef_exp ~iexc f se.se_gdef in
  if is_Land se.se_ev.ev_expr then (
    let conjs = destr_Land se.se_ev.ev_expr  in
    let (ineqs,eqs) = L.partition is_Not conjs in
    let nonZero = ref nz in
    let _ctx = { ic_pos = InEv; ic_isZero = []; ic_nonZero = nz } in
    let iter_ineq ineq =
      (* f ctx ineq; *) (* FIXME: useless for the case we are interested in *)
      match destr_Neq_norm ineq with
      | Some e ->
        nonZero := e :: !nonZero
      | None -> ()
    in
    L.iter iter_ineq ineqs;
    let ctx = { ic_pos = InEv; ic_isZero = []; ic_nonZero = !nonZero } in
    L.iter (f ctx) eqs
  ) else (
    let ctx = { ic_pos = InEv; ic_isZero = []; ic_nonZero = nz } in
    f ctx se.se_ev.ev_expr 
  )

(*i ----------------------------------------------------------------------- i*)
(* \hd{Equality} *) 

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

let obody_equal (c1,e1) (c2,e2) =
  lcmds_equal c1 c2 && e_equal e1 e2

let ohybrid_equal oh1 oh2 =
  obody_equal oh1.odef_less oh2.odef_less
  && obody_equal oh1.odef_eq oh2.odef_eq
  && obody_equal oh1.odef_greater oh2.odef_greater

let odecl_equal od1 od2 =
  match od1, od2 with
  | Odef ob1, Odef ob2 -> obody_equal ob1 ob2
  | Ohybrid oh1, Ohybrid oh2 -> ohybrid_equal oh1 oh2
  | _ -> false

let odef_equal (o1,xs1,od1) (o2,xs2,od2) =
  Osym.equal o1 o2 &&
    list_eq_for_all2 Vsym.equal xs1 xs2 &&
    odecl_equal od1 od2

let gcmd_equal i1 i2 =
  match i1, i2 with
  | GLet(x1,e1), GLet(x2,e2) ->
    Vsym.equal x1 x2 && e_equal e1 e2
  | GAssert(e1), GAssert(e2) ->
    e_equal e1 e2
  | GSamp(x1,d1), GSamp(x2,d2) ->
    Vsym.equal x1 x2 && distr_equal d1 d2
  | GCall(xs1,as1,e1,od1), GCall(xs2,as2,e2,od2) ->
    list_eq_for_all2 Vsym.equal xs1 xs2 &&
      e_equal e1 e2 &&
      list_eq_for_all2 odef_equal od1 od2 &&
      Asym.equal as1 as2
  | GLet _, (GSamp _ | GCall _ | GAssert _)  
  | GAssert _, (GLet _ | GCall _ | GSamp _) 
  | GSamp _, (GLet _ | GCall _ | GAssert _) 
  | GCall _, (GLet _ | GSamp _ | GAssert _) -> false

let gdef_equal c1 c2 = list_eq_for_all2 gcmd_equal c1 c2

let ev_equal ev1 ev2 =
  let b_equal (xs1,ors1) (xs2,ors2) =
    (Oracle.equal ors1 ors2) &&
    try List.for_all2 Vsym.equal xs1 xs2
    with Invalid_argument _ -> false in
  ev1.ev_quant = ev2.ev_quant &&
  e_equal ev1.ev_expr ev2.ev_expr &&
  try List.for_all2 b_equal ev1.ev_binding ev2.ev_binding
  with Invalid_argument _ -> false

let se_equal se1 se2 =
  gdef_equal se1.se_gdef se2.se_gdef &&
    ev_equal se1.se_ev se2.se_ev

(*i ----------------------------------------------------------------------- i*)
(* \hd{Read and write variables } *)

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

let read_obody xs (lcmd,e) =
  let r = Se.union (read_lcmds lcmd) (e_vars e) in
  let w = Se.union (add_binding xs) (write_lcmds lcmd) in
  Se.diff r w 

let read_ohybrid xs oh =
  Se.union (read_obody xs oh.odef_less)
    (Se.union (read_obody xs oh.odef_eq) (read_obody xs oh.odef_greater))

let read_odecl xs od =
  match od with
  | Odef od -> read_obody xs od
  | Ohybrid oh -> read_ohybrid xs oh

(** We assume oracles do not overshadow variables from main. *)
let read_odef (_,xs,odecl) =
  read_odecl xs odecl

let read_odefs odefs = fold_union read_odef odefs

(** Main body. *)

let read_gcmd = function
  | GLet(_,e)         -> e_vars e 
  | GAssert(e)        -> e_vars e
  | GSamp(_,d)        -> read_distr d
  | GCall(_,_,e,odefs) -> Se.union (e_vars e) (read_odefs odefs)

let read_gcmds c = fold_union read_gcmd c

let write_gcmd = function
  | GLet (x,_) | GSamp (x,_) -> Se.singleton (mk_V x)
  | GAssert(_)               -> Se.empty
  | GCall (xs,_,_,_)         -> add_binding xs

let write_gcmds c = fold_union write_gcmd c

let asym_gcmd gcmd =
  match gcmd with
  | GCall(_,asym,_,_) -> Some asym
  | _                 -> None

let asym_gcmds gcmds =
  L.map asym_gcmd gcmds |> catSome

(** Sedgments. *)

let read_se se = Se.union (read_gcmds se.se_gdef) (e_vars se.se_ev.ev_expr)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Hash call (hc) occurences} *)
let fold_union_hc f hcs =
  L.fold_right Hsym.S.union (L.map f hcs) Hsym.S.empty

let expr_hash_calls  e =
  let fst (a,_) = a in          
  Se.fold (fun e s -> Hsym.S.add (fst(destr_H e)) s) (e_hash_calls e) Hsym.S.empty

let exprs_hash_calls es = fold_union_hc expr_hash_calls es

let lcmd_hash_calls = function 
  | LLet(_,e)   -> expr_hash_calls e
  | LSamp(_,d)  -> exprs_hash_calls (snd d)
  | LBind _ -> Hsym.S.empty
  | LGuard(e)   -> expr_hash_calls e

let lcmds_hash_calls c = fold_union_hc lcmd_hash_calls c

let obody_hash_calls (cmds,e) =
  (Hsym.S.union (expr_hash_calls e) (lcmds_hash_calls cmds))

let ohybrid_hash_calls oh =
  Hsym.S.union (obody_hash_calls oh.odef_less)
    (Hsym.S.union (obody_hash_calls oh.odef_eq) (obody_hash_calls oh.odef_greater))

let odecl_hash_calls od =
  match od with
  | Odef od -> obody_hash_calls od
  | Ohybrid oh -> ohybrid_hash_calls oh

let odef_hash_calls (_,_,odecl) =
  odecl_hash_calls odecl 

let gcmd_all_hash_calls = function
  | GLet(_,e)  -> expr_hash_calls e
  | GAssert(e) -> expr_hash_calls e
  | GSamp(_,d) -> exprs_hash_calls (snd d)
  | GCall(_,_,e,odefs) ->
    Hsym.S.union
      (fold_union_hc odef_hash_calls odefs)
      (expr_hash_calls e)

let gdef_all_hash_calls gdef = fold_union_hc gcmd_all_hash_calls gdef

let ohybrid_global_hash_calls oh =
  (obody_hash_calls oh.odef_eq)

let odef_global_hash_calls (_,_vs,odecl) =
  match odecl with
  | Odef _ -> Hsym.S.empty
  | Ohybrid oh ->
    ohybrid_global_hash_calls oh

let gcmd_global_hash_calls = function
  | GLet(_,e)  -> expr_hash_calls e
  | GAssert(e) -> expr_hash_calls e
  | GSamp(_,d) -> exprs_hash_calls (snd d)
  | GCall(_,_,e,odefs) ->
    Hsym.S.union
      (fold_union_hc odef_global_hash_calls odefs)
      (expr_hash_calls e) 

let gdef_global_hash_calls gdef = fold_union_hc gcmd_global_hash_calls gdef


(* \hd{Expr args in Hash call (hc) occurences of hash function h} *)
let fold_union_hc_h f hcs =
  L.fold_right Se.union (L.map f hcs) Se.empty

let expr_hash_calls_h h e =
  let aux e s =
    let h1,e1 = destr_H e in
    if Hsym.equal h h1 then Se.add e1 s else s in 
  Se.fold aux (e_hash_calls e) Se.empty

let exprs_hash_calls_h h es = fold_union_hc_h (expr_hash_calls_h h) es

let lcmd_hash_calls_h h = function 
  | LLet(_,e)   -> expr_hash_calls_h h e
  | LSamp(_,d)  -> exprs_hash_calls_h h (snd d)
  | LBind _ -> Se.empty
  | LGuard(e)   -> expr_hash_calls_h h e

let lcmds_hash_calls_h h c = fold_union_hc_h (lcmd_hash_calls_h h) c

let obody_hash_calls_h h (cmds,e) =
  (Se.union (expr_hash_calls_h h e) (lcmds_hash_calls_h h cmds))

let ohybrid_hash_calls_h h oh =
  Se.union (obody_hash_calls_h h oh.odef_less)
    (Se.union (obody_hash_calls_h h oh.odef_eq) (obody_hash_calls_h h oh.odef_greater))

let odecl_hash_calls_h h od =
  match od with
  | Odef od -> obody_hash_calls_h h od
  | Ohybrid oh -> ohybrid_hash_calls_h h oh

let odef_hash_calls_h h (_,_,odecl) =
  odecl_hash_calls_h h odecl 

let gcmd_all_hash_calls_h h = function
  | GLet(_,e)  -> expr_hash_calls_h h e
  | GAssert(e) -> expr_hash_calls_h h e
  | GSamp(_,d) -> exprs_hash_calls_h h (snd d)
  | GCall(_,_,e,odefs) ->
    Se.union
      (fold_union_hc_h (odef_hash_calls_h h) odefs)
      (expr_hash_calls_h h e)

let gdef_all_hash_calls_h h gdef = fold_union_hc_h (gcmd_all_hash_calls_h h) gdef

let ohybrid_global_hash_calls_h h oh =
  (obody_hash_calls_h h oh.odef_eq)

let odef_global_hash_calls_h h (_,_,odecl) =
  match odecl with
  | Odef _ -> Se.empty
  | Ohybrid oh ->
    ohybrid_global_hash_calls_h h oh

let gcmd_global_hash_calls_h h = function
  | GLet(_,e)  -> expr_hash_calls_h h e
  | GAssert(e) -> expr_hash_calls_h h e
  | GSamp(_,d) -> exprs_hash_calls_h h (snd d)
  | GCall(_,_,e,odefs) ->
    Se.union
      (fold_union_hc_h (odef_global_hash_calls_h h) odefs)
      (expr_hash_calls_h h e) 

let gdef_global_hash_calls_h h gdef = fold_union_hc_h (gcmd_global_hash_calls_h h) gdef

(* \hd{Variable occurences} *) 

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

let obody_vars (cmd,e) =
  (Vsym.S.union (expr_vars e) (lcmds_vars cmd))

let ohybrid_vars oh =
  Vsym.S.union (obody_vars oh.odef_less)
    (Vsym.S.union (obody_vars oh.odef_eq) (obody_vars oh.odef_greater))

let odecl_vars od =
  match od with
  | Odef od -> obody_vars od
  | Ohybrid oh -> ohybrid_vars oh

let odef_vars (_,vs,odecl) =
  Vsym.S.union (set_of_list vs) (odecl_vars odecl)

let gcmd_all_vars = function
  | GLet(v,e)  -> Vsym.S.add v (expr_vars e)
  | GAssert(e) -> expr_vars e
  | GSamp(v,d) -> Vsym.S.add v (exprs_vars (snd d))
  | GCall(vs,_,e,odefs) ->
    Vsym.S.union
      (fold_union_vs odef_vars odefs)
      (Vsym.S.union (expr_vars e) (set_of_list vs))

let gdef_all_vars gdef = fold_union_vs gcmd_all_vars gdef

let obody_vars (cmd,e) =
  (Vsym.S.union (expr_vars e) (lcmds_vars cmd))

let ohybrid_global_vars oh =
  (obody_vars oh.odef_eq)

let odef_global_vars (_,vs,odecl) =
  match odecl with
  | Odef _ -> Vsym.S.empty
  | Ohybrid oh ->
    Vsym.S.union (set_of_list vs) (ohybrid_global_vars oh)

let gcmd_global_vars = function
  | GLet(v,e)  -> Vsym.S.add v (expr_vars e)
  | GAssert(e) -> expr_vars e
  | GSamp(v,d) -> Vsym.S.add v (exprs_vars (snd d))
  | GCall(vs,_,e,odefs) ->
    Vsym.S.union
      (fold_union_vs odef_global_vars odefs)
      (Vsym.S.union (expr_vars e) (set_of_list vs))

let gdef_global_vars gdef = fold_union_vs gcmd_global_vars gdef

(*i ----------------------------------------------------------------------- i*)
(* \hd{Unification} *) 

let ensure_same_length l1 l2 =
  if L.length l1 <> L.length l2 then raise Not_found

let unif_vs ren v1 v2 =
  if not (Vsym.equal v1 v2) then
    Vsym.H.add ren v1 v2

(* FIXME: pretty incomplete *)
let unif_expr _ren _e1 _e2 = ()
  (* match e1.e_node, e2.e_node with
     | Exists(_,_,binders1), Exists(_,_,binders2) ->
        ensure_same_length binders1 binders2;
        L.iter2 (unif_vs ren) (L.map fst binders1) (L.map fst binders2)
     | _ -> () *)

let unif_lcmd ren lc1 lc2 =
  match lc1,lc2 with
  | LLet(v1,_), LLet(v2,_)
  | LSamp(v1,_), LSamp(v2,_) ->
    unif_vs ren v1 v2
  | LBind(vss1,_), LBind(vss2,_) ->
    ensure_same_length vss1 vss2;
    L.iter2 (unif_vs ren) vss1 vss2
  | LGuard(_), LGuard(_) ->
    ()
  | _ -> 
    raise Not_found

let unif_obody ren (lcmds1,_) (lcmds2,_) = 
  ensure_same_length lcmds1 lcmds2;
  L.iter2 (unif_lcmd ren) lcmds1 lcmds2

let unif_odecl ren odecl1 odecl2 =
  match odecl1, odecl2 with
  | Odef ob1,    Odef ob2    -> unif_obody ren ob1 ob2
  | Ohybrid oh1, Ohybrid oh2 ->
    unif_obody ren oh1.odef_less    oh2.odef_less;
    unif_obody ren oh1.odef_eq      oh2.odef_eq;
    unif_obody ren oh1.odef_greater oh2.odef_greater
  | _, _ -> raise Not_found

let unif_odef ren (_,vs1,od1) (_,vs2,od2) =
  ensure_same_length vs1 vs2;
  L.iter2 (unif_vs ren) vs1 vs2;
  unif_odecl ren od1 od2

let unif_gcmd ren gcmd1 gcmd2 =
  match gcmd1, gcmd2 with
  | GLet(v1,_), GLet(v2,_)
  | GSamp(v1,_), GSamp(v2,_) -> unif_vs ren v1 v2
  | GAssert(_), GAssert(_) -> ()
  | GCall(vs1,_,_,odefs1), GCall(vs2,_,_,odefs2) ->
    ensure_same_length vs1 vs2;
    ensure_same_length odefs1 odefs2;
    L.iter2 (unif_vs ren) vs1 vs2;
    L.iter2 (unif_odef ren) odefs1 odefs2
  | _ -> raise Not_found

let unif_gdef ren gd1 gd2 =
  ensure_same_length gd1 gd2;
  L.iter2 (unif_gcmd ren) gd1 gd2

let vht_to_map ht =
  Vsym.H.fold (fun v x m -> Vsym.M.add v x m) ht Vsym.M.empty

(** We only support an outermost exists binder *)
let unif_se se1 se2 =
  try 
    let ren = Vsym.H.create 134 in
    unif_gdef ren se1.se_gdef se2.se_gdef;
    unif_expr ren se1.se_ev se2.se_ev;
    vht_to_map ren
  with
    Not_found ->
      F.printf "no unifier found!\n%!";
      raise Not_found 

let unif_gdef g1 g2 = 
  let ren = Vsym.H.create 134 in
  unif_gdef ren g1 g2;
  vht_to_map ren
  
let ren_injective sigma =
  try
    let inv = Vsym.H.create 134 in
    Vsym.M.iter
      (fun _ v' ->
        if Vsym.H.mem inv v'
        then raise Not_found
        else Vsym.H.add inv v' ())
      sigma;
    true
  with
    Not_found ->
      false

(*i ----------------------------------------------------------------------- i*)
(* \hd{Variable renaming} *)

let subst_v_e tov =
  let aux e =
    match e.e_node with
    | V v -> mk_V (tov v)
    (*i we could reorder n-ary constructors here after the renaming
    | Nary(o, es) when o == FPlus || o == FMult || o == GMult || o == Xor ->
      let es = L.map (e_map_top aux) es in
      Expr.mk_nary "subst" true o (L.sort e_compare es) (L.hd es).e_ty i*)
    (*
    | Exists(e1,e2,binders) ->
      let e1 = e_map_top aux e1 in
      let e2 = e_map_top aux e2 in
      mk_Exists e1 e2 (L.map (fun (v,h) -> (tov v,h)) binders)
    *)
    | _   -> raise Not_found
  in
  e_map_top aux

let subst_v_lc tov = function
  | LLet (v, e) -> LLet(tov v, subst_v_e tov e)
  | LBind (vs,lh) -> LBind (L.map tov vs, lh)
  | LSamp(v,d) -> LSamp(tov v, map_distr_exp (subst_v_e tov) d)
  | LGuard e -> LGuard (subst_v_e tov e)

let subst_v_obody tov (lc,e) =
  let lc = L.map (subst_v_lc tov) lc in
  let e = subst_v_e tov e in
  (lc, e)

let subst_v_odecl tov od =
  match od with
  | Odef ob    -> Odef (subst_v_obody tov ob)
  | Ohybrid oh -> Ohybrid (map_ohybrid (subst_v_obody tov) oh)

let subst_v_odef tov (o,vs,od) =
  let vs = L.map tov vs in
  let od = subst_v_odecl tov od in
  (o, vs, od)

let subst_v_gc tov = function
  | GLet(v,e) -> GLet(tov v, subst_v_e tov e)
  | GAssert(e) -> GAssert(subst_v_e tov e)
  | GSamp(v, d) -> GSamp(tov v, map_distr_exp (subst_v_e tov) d)
  | GCall(vs, asym, e, odefs) ->
    GCall(L.map tov vs, asym, subst_v_e tov e,
          L.map (subst_v_odef tov) odefs)

let subst_v_gdef tov = L.map (subst_v_gc tov)

let subst_v_ev tov ev = 
  { ev with ev_expr = subst_v_e tov ev.ev_expr }
 
let subst_v_se tov se =
  { se_gdef = subst_v_gdef tov se.se_gdef; se_ev = subst_v_ev tov se.se_ev }

(** Renaming of variables. *)
type renaming = vs Vsym.M.t

let id_renaming = Vsym.M.empty

let pp_ren fmt ren =
  pp_list "," (pp_pair Vsym.pp Vsym.pp) fmt (Vsym.M.bindings ren)

(* \hd{check_hash_args rule helper : Replace hash calls by lookups} *)

let subst_lkup_e to_lkup =
  let aux e =
    match e.e_node with
    | H(hs,e) when (Hsym.is_ro hs) -> mk_H (to_lkup (hs,e)) e
    (*i we could reorder n-ary constructors here after the renaming
    | Nary(o, es) when o == FPlus || o == FMult || o == GMult || o == Xor ->
      let es = L.map (e_map_top aux) es in
      Expr.mk_nary "subst" true o (L.sort e_compare es) (L.hd es).e_ty i*)
    (*
    | Exists(e1,e2,binders) ->
      let e1 = e_map_top aux e1 in
      let e2 = e_map_top aux e2 in
      mk_Exists e1 e2 (L.map (fun (v,h) -> (tov v,h)) binders)
    *)
    | _ -> e
  in
  e_map aux

let subst_lkup_lc to_lkup = function
  | LLet (v, e) -> LLet(v, subst_lkup_e to_lkup e)
  | LBind _ as lcmd' -> lcmd'
  | LSamp(v,d) -> LSamp(v, map_distr_exp (subst_lkup_e to_lkup) d)
  | LGuard e -> LGuard (subst_lkup_e to_lkup e)

let subst_lkup_lcmds to_lkup = L.map (subst_lkup_lc to_lkup)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Mappings from strings to variables} *) 

type vmap = (string qual * string,Vsym.t) Hashtbl.t

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
    (fun vs ->
       Hashtbl.add vm
         (map_qual (fun os -> Id.name os.Osym.id) vs.Vsym.qual, Vsym.to_string vs)
         vs)
    vss;
  vm

let vmap_of_ves ves =
  let vm = Hashtbl.create 134 in
  Se.iter
    (fun v ->
      let vs = destr_V v in
      Hashtbl.add vm
        (map_qual (fun os -> Id.name os.Osym.id) vs.Vsym.qual, Vsym.to_string vs)
        vs)
    ves;
  vm

let vmap_of_globals gdef = vmap_of_vss (gdef_global_vars gdef)

let vmap_of_se se = 
  let s = 
    List.fold_left (fun s (vs,_) -> 
      List.fold_left (fun s v -> Vsym.S.add v s) s vs)
      (gdef_global_vars se.se_gdef)
      se.se_ev.ev_binding in
  vmap_of_vss s

let ves_to_vss ves =
  Se.fold (fun e vss -> Vsym.S.add (destr_V e) vss) ves Vsym.S.empty

let vmap_in_orcl se op =
  let (i,_,_,_) = op in
  let gdef_before =
    let rbefore, _ = cut_n i se.se_gdef in
    L.rev rbefore
  in
  let _,seoc = get_se_octxt_len se op 0 in
  vmap_of_vss
    (Vsym.S.union
       (Vsym.S.union (gdef_global_vars gdef_before)
          (ves_to_vss (write_lcmds seoc.seoc_cleft)))
       (set_of_list seoc.seoc_oargs))

(*i ----------------------------------------------------------------------- i*)
(* \hd{Normal forms} *) 

let norm_distr ?norm:(nf=(Norm.norm_expr_nice)) s (ty,es) = 
  (ty, L.map (fun e -> nf (e_subst s e)) es)

let norm_obody ?norm:(nf=Norm.norm_expr_nice) s exported_defs (lc,e) =
  let do_export, add_export =
    match exported_defs with
    | None -> false, fun _ _ -> ()
    | Some map_r -> true, fun v e -> map_r := Me.add v e !map_r
  in
  let rec aux s rc ~do_export lc = 
    match lc with
    | [] -> (L.rev rc, nf (e_subst s e))
    | LLet (v, e) :: lc' ->
      let e = nf (e_subst s e) in
      let v = mk_V v in
      let s = Me.add v e s in
      add_export v e;
      aux s rc ~do_export lc' 
    | (LBind (vs,_) as i)::lc' -> 
      let s = L.fold_left (fun s v -> Me.remove (mk_V v) s) s vs in
      aux s (i::rc) ~do_export:false lc'
    | LSamp(v,d)::lc' ->
      let d = norm_distr ~norm:nf s d in
      let s = Me.remove (mk_V v) s in
      aux s (LSamp(v,d)::rc) ~do_export lc'
    | LGuard e::lc' ->
      aux s (LGuard (nf (e_subst s e)) :: rc) ~do_export:false lc' in
  aux s [] ~do_export lc

let norm_odef ?norm:(nf=Norm.norm_expr_nice) s exported_defs (o,vs,od) =
  let od =
    match od with
    | Odef ob -> Odef (norm_obody ~norm:nf s None ob)
    | Ohybrid oh ->
      Ohybrid
        { odef_less    = norm_obody ~norm:nf s None          oh.odef_less;
          odef_eq      = norm_obody ~norm:nf s exported_defs oh.odef_eq;
          odef_greater = norm_obody ~norm:nf s None          oh.odef_greater }
  in
  (o,vs,od)

let norm_gdef ?norm:(nf=Norm.norm_expr_nice) g =
  let rec aux s rc lc = 
    match lc with
    | [] -> L.rev rc, s
    | GLet(v,e) :: lc' ->
      let e = nf (e_subst s e) in
      let v = mk_V v in
      let s = Me.add v e s in
      aux s rc lc'
    | GAssert(e) :: lc' ->
      let e = nf (e_subst s e) in
      aux s (GAssert(e) :: rc) lc'
    | GSamp(v, d) :: lc' ->
      let d = norm_distr ~norm:nf s d in
      let s = Me.remove (mk_V v) s in
      aux s (GSamp(v,d) :: rc) lc'
    | GCall(vs, asym, e, odefs) :: lc'->
      let e = nf (e_subst s e) in
      let exported_defs = ref Me.empty in
      let odefs = L.map (norm_odef ~norm:nf s (Some exported_defs)) odefs in
      let s = Me.fold (fun k v s -> Me.add k v s) !exported_defs s in
      let s = L.fold_left (fun s v -> Me.remove (mk_V v) s) s vs in
      aux s (GCall(vs, asym, e, odefs)::rc) lc'
  in
  aux Me.empty [] g

let norm_se ?norm:(nf=Norm.norm_expr_nice) se =
  let g,s = norm_gdef ~norm:nf se.se_gdef in
  { se_gdef = g;
    se_ev = {se.se_ev with ev_expr = nf (e_subst s se.se_ev.ev_expr) } }

(*i ----------------------------------------------------------------------- i*)
(* \hd{Probabilistic polynomial time} *)

let has_log_distr (_,es) = L.exists has_log es
  
let has_log_lcmd = function
  | LLet(_,e) | LGuard e -> has_log e
  | LBind _              -> false
  | LSamp(_,d)           -> has_log_distr d

let has_log_lcmds c = L.exists has_log_lcmd c

let has_log_obody (cmd,e) = has_log e || has_log_lcmds cmd

let has_log_odecl od =
  match od with
  | Odef od -> has_log_obody od
  | Ohybrid oh -> L.exists has_log_obody [ oh.odef_less; oh.odef_eq; oh.odef_greater ]

let has_log_odef (_,_,od) = has_log_odecl od

let has_log_gcmd = function
  | GLet(_,e) | GAssert(e) -> has_log e
  | GSamp(_,d) -> has_log_distr d
  | GCall(_,_,e,ods) -> has_log e || L.exists has_log_odef ods

let has_log_gcmds c = L.exists has_log_gcmd c

let is_ppt_distr (_,es) = L.for_all is_ppt es
  
let is_ppt_lcmd = function
  | LLet(_,e) | LGuard e -> is_ppt e
  | LBind _              -> true
  | LSamp(_,d)           -> is_ppt_distr d

let is_ppt_lcmds c = L.for_all is_ppt_lcmd c

let is_ppt_obody (cmd,e) = is_ppt e && is_ppt_lcmds cmd

let is_ppt_odecl od =
  match od with
  | Odef ob -> is_ppt_obody ob
  | Ohybrid oh -> L.exists is_ppt_obody [ oh.odef_less; oh.odef_eq; oh.odef_greater ]

let is_ppt_odef (_,_,od) = is_ppt_odecl od

let is_ppt_gcmd = function
  | GLet(_,e) | GAssert(e) -> is_ppt e
  | GSamp(_,d) -> is_ppt_distr d
  | GCall(_,_,e,od) -> is_ppt e || L.for_all is_ppt_odef od

let is_ppt_gcmds c = L.for_all is_ppt_gcmd c

let is_ppt_se se = is_ppt_gcmds se.se_gdef && is_ppt se.se_ev.ev_expr 

let is_call = function
  | GCall _ -> true
  | _       -> false

let has_call c = L.exists is_call c

let is_assert = function
  | GAssert _ -> true
  | _         -> false

let has_assert c =  L.exists is_assert c

let destr_guard lcmd =
  match lcmd with
  | LGuard(e) -> e
  | _ -> assert false (* FIXME *)
