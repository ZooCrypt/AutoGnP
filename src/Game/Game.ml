(* * Cryptographic game definitions *)

(* ** Imports and Abbreviations*)
open Abbrevs
open Util
open Type
open Expr
open ExprUtils
open Syms

(** Variable, adversary, oracle, function, and oracle list symbols. *)
type vs  = Vsym.t
type ads = Asym.t
type os  = Osym.t
type hs  = Fsym.t
type ors = Olist.t

(* ** Types for oracles, games, and security 
 * ----------------------------------------------------------------------- *)

(** (Excepted) Distributions for sampling. *)
type distr = ty * expr list  (* uniform distr. over type except for given values *)
  with compare

(** List monad command for oracle definition. *)
type lcmd =
  | LLet   of vs * expr    (* LLet(xs,e):   let (x_1,..,x_k) = e *)
  | LBind  of vs list * hs (* LBind(xs, h): (x_1,..,x_k) <- L_h  *)
  | LSamp  of vs * distr   (* LSamp(x,d):   x <$ d               *)
  | LGuard of expr         (* LGuard(t):    guard(t)             *)
  with compare

(** Oracle body *)
type obody = lcmd list * Expr.expr (* (ms, e): m1; ..; mk; return e *)
  with compare

(** Oracle body for hybrid oracle *)
type ohybrid = {
  oh_less    : obody; (* oracle body for queries <i *)
  oh_eq      : obody; (* oracle body for queries =i *)
  oh_greater : obody; (* oracle body for queries >i *)
} with compare

(** Oracle declaration *)
type odecl =
  | Oreg of obody   (* regular oracle *)
  | Ohyb of ohybrid (* hybrid oracle *) 
  with compare

(** Oracle definition. *)
type odef = os * vs list * odecl
  (* (o,xs,ms,e): o(x_1,..,x_l) = [e | m_1, .., m_k] *)
  with compare

(** Game command. *)
type gcmd =
  | GLet    of vs * expr     (* GLet(xs,e):     let (x_1,..,x_k) = e             *)
  | GAssert of expr          (* GAssert(e):     assert(e)                        *)
  | GSamp   of vs * distr    (* GSamp(x,d):     x <$ d                           *)
  | GCall   of vs list * ads (* GCall(xs,e,os): (x1,..,xk) <@ A(e) with o1,..,ol *)
               * expr * odef list 
  with compare

(** Game definition. *)
type gdef = gcmd list

(** A security experiment consists of a game and an event. *)
type sec_exp = {
  se_gdef : gdef;
  se_ev   : expr;
} with compare


(* ** Equality and indicator functions *
 * ----------------------------------------------------------------------- *)

let distr_equal d1 d2 = compare_distr d1 d2 = 0

let lcmd_equal i1 i2 = compare_lcmd i1 i2 = 0

let lcmds_equal c1 c2 = list_eq_for_all2 lcmd_equal c1 c2

let obody_equal ob1 ob2 = compare_obody ob1 ob2 = 0

let ohybrid_equal oh1 oh2 = compare_ohybrid oh1 oh2 = 0

let odecl_equal od1 od2 = compare_odecl od1 od2 = 0

let odef_equal oh1 oh2 = compare_odef oh1 oh2 = 0

let gcmd_equal g1 g2 = compare_gcmd g1 g2 = 0

let gdef_equal c1 c2 = list_eq_for_all2 gcmd_equal c1 c2

let sec_exp_equal se1 se2 = compare_sec_exp se1 se2 = 0

let is_hybrid = function Onothyb -> false | Oishyb _ -> true

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

(** Hybrid oracle type *)
type ohtype = OHless | OHeq | OHgreater 

(** Oracle type *)
type otype = Onothyb | Oishyb of ohtype

(* ** Generic functions: [map_*_expr] and [iter_*_expr]
 * ----------------------------------------------------------------------- *)

(* *** map *)

let map_distr_exp f (t,es) = (t, L.map f es)

let map_lcmd_exp f = function
  | LLet(vs,e)  -> LLet(vs, f e)
  | LBind(vs,h) -> LBind(vs,h)
  | LSamp(v,d)  -> LSamp(v, map_distr_exp f d)
  | LGuard(e)   -> LGuard(f e)


let map_ohybrid f {oh_less; oh_eq; oh_greater} = {
  oh_less    = f oh_less;
  oh_eq      = f oh_eq;
  oh_greater = f oh_greater;
}

let map_obody_exp f (ms,e) =
  L.map (map_lcmd_exp f) ms, f e

let map_odecl_exp f = function
  | Oreg od -> Oreg (map_obody_exp f od)
  | Ohyb oh -> Ohyb (map_ohybrid (map_obody_exp f) oh)

let map_oh_exp f (o,vs,od) =
  (o,vs,map_odecl_exp f od)

let map_gcmd_exp f = function
  | GLet(vs,e)          -> GLet(vs, f e)
  | GAssert(e)          -> GAssert(f e)
  | GSamp(v,d)          -> GSamp(v, map_distr_exp f d)
  | GCall(vs,asym,e,os) -> GCall(vs, asym, f e, L.map (map_oh_exp f) os)

let map_gdef_exp f gdef =
  L.map (map_gcmd_exp f) gdef

let map_sec_exp f se = {
  se_gdef = map_gdef_exp f se.se_gdef;
  se_ev   = f se.se_ev;
}

(* *** iter *)

let iter_distr_exp ?iexc:(iexc=false) f (_,es) =
  if iexc then L.iter f es

let iter_lcmd_exp ?iexc:(iexc=false) f = function
  | LLet(_,e)  -> f e
  | LBind(_)   -> ()
  | LSamp(_,d) -> iter_distr_exp ~iexc f d
  | LGuard(e)  -> f e

let iter_obody_exp ?iexc:(iexc=false) f (ms,e) =
  L.iter (iter_lcmd_exp ~iexc f) ms; f e

let iter_ohybrid_exp ?iexc:(iexc=false) f { oh_less; oh_eq; oh_greater} =
  iter_obody_exp ~iexc f oh_less;
  iter_obody_exp ~iexc f oh_eq;
  iter_obody_exp ~iexc f oh_greater

let iter_odecl_exp ?iexc:(iexc=false) f = function
  | Oreg od -> iter_obody_exp ~iexc f od
  | Ohyb oh -> iter_ohybrid_exp ~iexc f oh

let iter_oh_exp ?iexc:(iexc=false) f (_o,_vs,od) =
  iter_odecl_exp ~iexc f od

let iter_gcmd_exp ?iexc:(iexc=false) f = function
  | GLet(_,e)
  | GAssert(e)      -> f e
  | GSamp(_,d)      -> iter_distr_exp ~iexc f d
  | GCall(_,_,e,od) -> f e; L.iter (iter_oh_exp ~iexc f) od

let iter_gcmd_exp_orcl ?iexc:(iexc=false) f = function
  | GLet(_,_)
  | GAssert(_)
  | GSamp(_,_)      -> ()
  | GCall(_,_,_,od) -> L.iter (iter_oh_exp ~iexc f) od

let iter_gcmd_exp_no_orcl ?iexc:(iexc=false) f gcmd = match gcmd with
  | GLet(_,e)
  | GAssert(e)
  | GCall(_,_,e,_) -> f e
  | GSamp(_,d)     -> iter_distr_exp ~iexc f d

let iter_gdef_exp ?iexc:(iexc=false) f gdef =
  L.iter (iter_gcmd_exp_no_orcl ~iexc f) gdef;
  L.iter (iter_gcmd_exp_orcl ~iexc f) gdef

let iter_se_exp ?iexc:(iexc=false) f se =
  iter_gdef_exp ~iexc f se.se_gdef; f se.se_ev

(* ** Positions and replacement functions
 * ----------------------------------------------------------------------- *)

type gcmd_pos = int

type oh_pos = (int * int)

type ocmd_pos = (int * int * int * otype)

type ocmd_pos_eq = (int * int * int)

let get_se_gcmd se p = L.nth se.se_gdef p

type se_ctxt = {
  sec_left  : gdef;
  sec_right : gdef;
  sec_ev    : expr
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
  | Onothyb,          Oreg ob -> ob
  | Oishyb OHless,    Ohyb oh -> oh.oh_less
  | Oishyb OHeq,      Ohyb oh -> oh.oh_eq
  | Oishyb OHgreater, Ohyb oh -> oh.oh_greater
  | _ -> assert false

let get_se_lcmd se (i,j,k,otype) = 
  match get_se_gcmd se i with
  | GCall(_,_,_,ods) ->
    let (o,vs,od) = L.nth ods j in
    let (ms,e) = get_obody od otype in
    o,vs,split_n k ms, e
  | _ -> assert false

type se_octxt = {
  seoc_asym      : ads;
  seoc_avars     : vs list;
  seoc_aarg      : expr;
  seoc_oleft     : odef list;
  seoc_oright    : odef list;
  seoc_obless    : obody option;
  seoc_obeq      : obody option;
  seoc_obgreater : obody option;
  seoc_osym      : os;
  seoc_oargs     : vs list;
  seoc_return    : expr;
  seoc_cleft     : lcmd list;
  seoc_cright    : lcmd list;
  seoc_sec       : se_ctxt
}

let get_se_octxt_len se (i,j,k,ootype) len = 
  match get_se_ctxt se i with
  | GCall(vsa,asym,e,os), sec ->
    let rohd, (o,vs,od), otl = split_n j os in
    let (ms,oe) = get_obody od ootype in
    let rhd, tl = cut_n (min k (List.length ms)) ms in
    let cmds,cright = cut_n len tl in
    let obless = match ootype with
      | Oishyb (OHeq |  OHgreater) -> Some (get_obody od (Oishyb OHless))
      | _ -> None
    in
    let obeq = match ootype with
      | Oishyb (OHless | OHgreater) -> Some (get_obody od (Oishyb OHeq))
      | _ -> None
    in
    let obgreater = match ootype with
      | Oishyb (OHless | OHeq) -> Some (get_obody od (Oishyb OHgreater))
      | _ -> None
    in
    let ctx =
      { seoc_asym      = asym;
        seoc_avars     = vsa;
        seoc_aarg      = e;
        seoc_oright    = rohd;
        seoc_oleft     = otl;
        seoc_obless    = obless;
        seoc_obeq      = obeq;
        seoc_obgreater = obgreater;
        seoc_osym      = o;
        seoc_oargs     = vs;
        seoc_return    = oe;
        seoc_cleft     = rhd;
        seoc_cright    = cright;
        seoc_sec       = sec }
    in
    L.rev cmds, ctx
  | _ -> assert false

let set_se_octxt lcmds c =
  let ms = L.rev_append c.seoc_cleft (lcmds@c.seoc_cright) in
  let ob = (ms,c.seoc_return) in
  let odecl =
    match c.seoc_obless, c.seoc_obeq,  c.seoc_obgreater with
    | None,    None,     None   -> Oreg ob
    | None,    Some oe, Some og -> Ohyb { oh_less = ob; oh_eq = oe; oh_greater = og }
    | Some ol, None,    Some og -> Ohyb { oh_less = ol; oh_eq = ob; oh_greater = og }
    | Some ol, Some oe, None    -> Ohyb { oh_less = ol; oh_eq = oe; oh_greater = ob }
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

(* ** Read and write variables
 * ----------------------------------------------------------------------- *)

(* *** General purpose functions. *)

let fold_union f es =
  L.fold_left (fun s e -> Se.union s (f e)) Se.empty es

let add_binding xs =
  fold_union (fun x -> Se.singleton (mk_V x)) xs

(* *** Distributions. *)

let read_distr (_,es) = fold_union e_vars es

(* *** Oracle definitions. *)

let read_lcmd = function 
  | LLet(_,e) | LGuard e -> e_vars e
  | LBind _              -> Se.empty
  | LSamp(_,d)           -> read_distr d

let read_lcmds c = fold_union read_lcmd c

let write_lcmd = function
  | LLet(x,_) | LSamp(x,_) -> Se.singleton (mk_V x) 
  | LBind (xs,_)           -> add_binding xs 
  | LGuard _               -> Se.empty

let write_lcmds c = fold_union write_lcmd c

let read_obody xs (lcmd,e) =
  let r = Se.union (read_lcmds lcmd) (e_vars e) in
  let w = Se.union (add_binding xs) (write_lcmds lcmd) in
  Se.diff r w 

let read_ohybrid xs oh =
  Se.union (read_obody xs oh.oh_less)
    (Se.union (read_obody xs oh.oh_eq) (read_obody xs oh.oh_greater))

let read_odecl xs = function
  | Oreg od -> read_obody xs od
  | Ohyb oh -> read_ohybrid xs oh

(** We assume oracles do not overshadow variables from main. *)
let read_odef (_,xs,odecl) =
  read_odecl xs odecl

let read_odefs odefs = fold_union read_odef odefs

(* *** Main body. *)

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

let asym_gcmd = function
  | GCall(_,asym,_,_) -> Some asym
  | _                 -> None

let asym_gcmds gcmds =
  L.map asym_gcmd gcmds |> catSome

(* *** Security experiments *)

let read_se se = Se.union (read_gcmds se.se_gdef) (e_vars se.se_ev)

(* ** Find expressions that satisfy predicate
 * ----------------------------------------------------------------------- *)

let fold_union_e f xs =
  L.fold_right Se.union (L.map f xs) Se.empty

let expr_find p e = e_find_all p e

let exprs_find p es = fold_union_e (expr_find p) es

let lcmd_find p = function 
  | LLet(_,e)  -> expr_find p e
  | LSamp(_,d) -> exprs_find p (snd d)
  | LBind(_,_) -> Se.empty
  | LGuard(e)  -> expr_find p e

let lcmds_find p c = fold_union_e (lcmd_find p) c

let obody_find p (cmd,e) =
  Se.union (expr_find p e) (lcmds_find p cmd)

let ohybrid_find p oh =
  Se.union (obody_find p oh.oh_less)
    (Se.union (obody_find p oh.oh_eq) (obody_find p oh.oh_greater))

let odecl_find p = function
  | Oreg od -> obody_find p od
  | Ohyb oh -> ohybrid_find p oh

let oh_find p (_,_,odecl) = odecl_find p odecl

let gcmd_all_find p = function
  | GLet(_,e)  -> expr_find p e
  | GAssert(e) -> expr_find p e
  | GSamp(_,d) -> exprs_find p (snd d)
  | GCall(_,_,e,odefs) ->
    Se.add e (fold_union_e (oh_find p) odefs)

let gdef_all_find p gdef =
  fold_union_e (gcmd_all_find p) gdef

let ohybrid_global_find p oh =
  obody_find p oh.oh_eq

let oh_global_find p (_,_,odecl) =
  match odecl with
  | Oreg _  -> Se.empty
  | Ohyb oh -> ohybrid_global_find p oh

let gcmd_global_find p = function
  | GLet(_,e)  -> expr_find p e
  | GAssert(e) -> expr_find p e
  | GSamp(_,d) -> exprs_find p (snd d)
  | GCall(_,_,e,odefs) ->
    Se.add e (fold_union_e (oh_global_find p) odefs)

let gdef_global_find p gdef = fold_union_e (gcmd_global_find p) gdef

(* ** Random oracle symbol occurences in RO calls
 * ----------------------------------------------------------------------- *)

let ro_syms_of_es es =
  Se.fold (fun e s -> ROsym.S.add (fst (destr_RoCall e)) s) es ROsym.S.empty

let expr_ro_syms e = ro_syms_of_es (expr_find is_RoCall e)

let gcmd_all_ro_syms gcmd = ro_syms_of_es (gcmd_all_find is_RoCall gcmd)

let gdef_all_ro_syms gdef = ro_syms_of_es (gdef_all_find is_RoCall gdef)

let gdef_global_ro_syms gdef = ro_syms_of_es (gdef_global_find is_RoCall gdef)

(* ** Random oracle arguments for given RO symbol
 * ----------------------------------------------------------------------- *)

let harg_of_es es =
  Se.fold (fun e s ->
           if is_RoCall e then Se.add (snd (destr_RoCall e)) s
           else s) es Se.empty

let is_H_call h e = is_RoCall e && ROsym.equal h (fst (destr_RoCall e))

let expr_hash_args h e = harg_of_es (expr_find (is_H_call h) e)

let gcmd_all_hash_args h gcmd = harg_of_es (gcmd_all_find (is_H_call h) gcmd)

let gdef_all_hash_args h gdef = harg_of_es (gdef_all_find (is_H_call h) gdef)

let gdef_global_hash_args h gdef = harg_of_es (gdef_global_find (is_H_call h) gdef)

(* ** Variable occurences
 * ----------------------------------------------------------------------- *)

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
  Vsym.S.union (obody_vars oh.oh_less)
    (Vsym.S.union (obody_vars oh.oh_eq) (obody_vars oh.oh_greater))

let odecl_vars od =
  match od with
  | Oreg od -> obody_vars od
  | Ohyb oh -> ohybrid_vars oh

let oh_vars (_,vs,odecl) =
  Vsym.S.union (set_of_list vs) (odecl_vars odecl)

let gcmd_all_vars = function
  | GLet(v,e)  -> Vsym.S.add v (expr_vars e)
  | GAssert(e) -> expr_vars e
  | GSamp(v,d) -> Vsym.S.add v (exprs_vars (snd d))
  | GCall(vs,_,e,odefs) ->
    Vsym.S.union
      (fold_union_vs oh_vars odefs)
      (Vsym.S.union (expr_vars e) (set_of_list vs))

let gdef_all_vars gdef = fold_union_vs gcmd_all_vars gdef

let obody_vars (cmd,e) =
  (Vsym.S.union (expr_vars e) (lcmds_vars cmd))

let ohybrid_global_vars oh =
  (obody_vars oh.oh_eq)

let oh_global_vars (_,vs,odecl) =
  match odecl with
  | Oreg _  -> Vsym.S.empty
  | Ohyb oh -> Vsym.S.union (set_of_list vs) (ohybrid_global_vars oh)

let gcmd_global_vars = function
  | GLet(v,e)  -> Vsym.S.add v (expr_vars e)
  | GAssert(e) -> expr_vars e
  | GSamp(v,d) -> Vsym.S.add v (exprs_vars (snd d))
  | GCall(vs,_,e,odefs) ->
    Vsym.S.union
      (fold_union_vs oh_global_vars odefs)
      (Vsym.S.union (expr_vars e) (set_of_list vs))

let gdef_global_vars gdef = fold_union_vs gcmd_global_vars gdef

(* ** Variable renaming
 * ----------------------------------------------------------------------- *)

let subst_v_e tov =
  let aux e =
    match e.e_node with
    | V v -> mk_V (tov v)
    | _   -> raise Not_found
  in
  e_map_top aux

let subst_v_lc tov = function
  | LLet (v, e)   -> LLet(tov v, subst_v_e tov e)
  | LBind (vs,lh) -> LBind (L.map tov vs, lh)
  | LSamp(v,d)    -> LSamp(tov v, map_distr_exp (subst_v_e tov) d)
  | LGuard e      -> LGuard (subst_v_e tov e)

let subst_v_obody tov (lc,e) =
  let lc = L.map (subst_v_lc tov) lc in
  let e = subst_v_e tov e in
  (lc, e)

let subst_v_odecl tov = function
   Oreg ob -> Oreg (subst_v_obody tov ob)
  | Ohyb oh -> Ohyb (map_ohybrid (subst_v_obody tov) oh)

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

let subst_v_ev tov = subst_v_e tov
 
let subst_v_se tov se = {
  se_gdef = subst_v_gdef tov se.se_gdef;
  se_ev   = subst_v_ev tov se.se_ev;
}

type renaming = vs Vsym.M.t

let id_renaming = Vsym.M.empty

let pp_ren fmt ren =
  pp_list "," (pp_pair Vsym.pp Vsym.pp) fmt (Vsym.M.bindings ren)

(* ** Old *)
(* *** Event module *)

(*
module Event = struct
  type t = expr

  let mk_from_expr (e : expr) : t = e

  let mk ?quant ?binding e = match quant,binding with
    | None,None -> mk_from_expr e
    | Some q,Some b -> mk_Quant q b (mk_from_expr e)
    | _ -> invalid_arg "Event.mk"

  let equal = Expr.e_equal

  let quant ev = match ev.e_node with
    | Quant(q,_,_) -> q
    | _ -> Expr.All

  let rec binding ev = match ev.e_node with
    | Quant(_,b,e) -> b :: (binding e)
    | _ -> []

  let rec expr ev = match ev.e_node with
    | Quant(_,_,e) -> expr e
    | _ -> ev
               
  let rec map f ev = match ev.e_node with
    | Quant(q,b,e) -> mk_Quant q b (map f e)
    | _ -> f ev

  let rec insert ?quant ?binding ?e ev =
    match quant,binding,e with
    | None,   None,   Some e -> map (fun x -> mk_Land [x;e]) ev
    | Some q, Some b, _      -> insert ?e (map (mk_Quant q b) ev)
    | None,   None,   None   -> ev
    | _                      -> invalid_arg "Event.insert"
                       
  let set_expr e ev = map (fun _ -> e) ev

  let nth i ev =
    let evs = destr_Land_nofail (expr ev) in
    let _,e,_ = Util.split_n i evs in
    e
                                          
  let set_nth_aux i e0 e =
    let evs = destr_Land_nofail e in
    let l,_,r = Util.split_n i evs in
    mk_Land (List.rev_append l (e0::r))

  let set_nth i e = map (set_nth_aux i e)

  exception NoQuant

  let destr_exn ev =
    try  ExprUtils.destr_Quant ev
    with Destr_failure _ -> raise NoQuant

  let destr ev =
    try  Some (ExprUtils.destr_Quant ev)
    with Destr_failure _ -> None

  let pp_q fmt = function
    | All -> F.fprintf fmt "forall"
    | Exists -> F.fprintf fmt "exists"

  let pp_vs fmt = function
    | [v] -> Vsym.pp fmt v
    |  vs -> (pp_list "," Vsym.pp) fmt vs                                     

  let pp_b fmt (vs,o) = 
    F.fprintf fmt "%a in L_%a" pp_vs vs Oracle.pp o

  let rec pp fmt ev = match ev.e_node with
    | Quant(q,b,e) -> F.fprintf fmt "@[<hov>%a (%a):@ %a@]" pp_q q pp_b b pp e
    | _ -> pp_exp fmt ev
end
*)


(* *** Replace hash calls by lookups
 * ----------------------------------------------------------------------- *)

(*
let subst_lkup_e to_lkup =
  let aux e =
    match e.e_node with
    | H(hs,e) when (Fsym.is_ro hs) -> mk_H (to_lkup (hs,e)) e
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
 *)
