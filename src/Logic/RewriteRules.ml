(*s Derived tactics for rewriting. *)

(*i*)
open Abbrevs
open Util
open Game
open CoreTypes
open CoreRules
open Expr
open ExprUtils
open Norm
open NormField

module Ht = Hashtbl

let log_t ls = mk_logger "Logic.Derived" Bolt.Level.TRACE "RewriteRules" ls
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Derived rewriting tactics} *)

(** Unfold all lets and norm. *)
let t_norm ?fail_eq:(fe=false) ju =
  let se = ju.ju_se in
  let new_se = norm_se ~norm:norm_expr_nice se in
  if fe && se_equal se new_se
  then t_fail "t_norm: equal judgments" ju
  else t_conv true new_se ju

(** Unfold all lets and norm, also remove tuple projection. *)
let t_norm_tuple_proj ju = 
  let se = ju.ju_se in
  let norm e = remove_tuple_proj (norm_expr_nice e) in
  let new_se = norm_se ~norm se in
  t_conv true new_se ju

(** Norm without unfolding. *)
let t_norm_nounfold ju = 
  let se = ju.ju_se in
  let new_se = map_se_exp norm_expr_nice se in
  t_conv true new_se ju

(** Unfold without norm. *)
let t_unfold_only ju = 
  let se = ju.ju_se in
  let new_se = norm_se ~norm:id se in
  t_conv false new_se ju

(*i [simp e unknown] takes an exponent expression [e] and a
   set [unknown] of unknown expressions.
   It returns a pair [(ges,mdenom)] where [mdenom] is 
   a denominator using [None] to encode [1] and [ges] is a
   list of of triples (b,ue,ke) representing (b^ue)^ke
   where [None] encodes the default group generator.
   The whole list [ges] represent the product of group
   elements in [ges]. i*)
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
      let get_gen og = match og with None -> gen | Some a -> a in
      let expio b ie moe =
        let g = get_gen b in
        match moe with
        | Some oe -> mk_GExp (mk_GExp g ie) oe
        | None    -> mk_GExp g ie
      in
      let a =
        match ies with
        | []         -> gen
        | [b,ie,moe] -> expio b ie moe
        | ies        ->
          (* merge elements with the same base *)
          let iess =
            group (fun (e1,_,oe1) (e2,_,oe2) ->
              oe1 = None && oe2 = None && e_equal (get_gen e1) (get_gen e2)) ies
          in
          let combine_group ies =
            match ies with
            | (b,_,None)::_ ->
              expio b (mk_FPlus (L.map (fun (_,ie,moe) -> assert (moe = None); ie) ies)) None
            | [ (b,ie,moe)]  ->
              expio b ie moe
            | _ -> assert false
          in 
          mk_GMult (List.map combine_group iess)
      in
      begin match ce with
      | None    -> a
      | Some oe -> mk_GExp a (mk_FInv oe)
      end
    | _ -> e
  in
  go e0

(*i norm and try to rewrite all exponentiations as products of
   (g^i)^o or X where i might be unknown, but o is not unknown.
   If there is a "let z=g^i" we can replace g^i by z in the next
   step. i*)
let t_norm_unknown unknown ju =
  let se = ju.ju_se in
  let norm e = remove_tuple_proj (abbrev_ggen (rewrite_exps (se_of_list unknown) (norm_expr_weak e))) in
  let new_se = map_se_exp norm se in
  t_conv true new_se ju

let rewrite_div_reduce a e =
  let solve a e =
    assert (Type.is_Fq e.e_ty);
    let (p1,p2) = polys_of_field_expr e in
    let (a1,a2) = polys_of_field_expr a in
    if a2 <> None then e
    else
      let g = div_factor p1 a1 in
      let f = reduce p1 a1 in
      let mult = if e_equal (mk_FNat 1) g then a else mk_FMult [g; a] in
      let res =
        if e_equal (mk_FNat 0) g then (exp_of_poly p1)
        else if e_equal (mk_FNat 0) f then mult
        else mk_FPlus [mult; f]
      in
      match p2 with
      | None -> res
      | Some d ->
        let e' = mk_FDiv res (exp_of_poly d) in
        e'
  in
  e_map_ty_maximal Type.mk_Fq (solve a) e

(*i normalize field expressions (in exponents and elsewhere such that polynomials are
    expressed as a*f + g i*)
let t_norm_solve a ju =
  let se = ju.ju_se in
  let norm e = abbrev_ggen (rewrite_div_reduce (norm_expr_weak a) (norm_expr_weak e)) in
  let new_se = map_se_exp norm se in
  t_conv true new_se ju

let t_let_abstract p vs e mupto do_norm_expr ju =
  let se = ju.ju_se in
  let v = mk_V vs in
  let e = if do_norm_expr then remove_tuple_proj (norm_expr_nice e) else e in
  let subst a =
    if is_Tuple e then (
      let subst = me_of_list (L.mapi (fun i a -> (a,mk_Proj i v)) (destr_Tuple e)) in
      e_subst subst a
    ) else (
      e_replace e v a
    )
  in
  log_t (lazy (fsprintf "t_let_abstr: %a" pp_exp e));
  let l,r = Util.cut_n p se.se_gdef in
  let new_ju =
    match mupto with
    | Some j ->
      log_t (lazy (fsprintf "<< %i" j));
      if (j < p) then tacerror "t_let_abstract: invalid upto %i" j;
      let cl = j - p in
      if (cl > L.length r) then tacerror "t_let_abstract: invalid upto %i" j;
      let r1,r2 = Util.cut_n cl r in
      let r = List.rev_append (map_gdef_exp subst r1) r2 in
      { se_gdef = List.rev_append l (GLet(vs,e)::r);
        se_ev = se.se_ev }
    | None ->
      { se_gdef = List.rev_append l (GLet(vs,e)::map_gdef_exp subst r);
        se_ev = subst se.se_ev }
  in
  t_conv true new_ju ju

let t_subst p e1 e2 mupto ju =
  let se = ju.ju_se in
  let subst a = e_replace e1 e2 a in
  let l,r = cut_n p se.se_gdef in
  let new_se = 
    match mupto with
    | Some j ->
      if (j < p) then tacerror "t_let_abstract: invalid upto %i" j;
      let cl = j - p in
      if (cl > L.length r) then tacerror "t_let_abstract: invalid upto %i" j;
      let r1,r2 = Util.cut_n cl r in
      let r = List.rev_append (map_gdef_exp subst r1) r2 in
      { se_gdef = List.rev_append l r;
        se_ev = se.se_ev }
    | None ->
      { se_gdef = L.rev_append l (map_gdef_exp subst r);
        se_ev   = subst se.se_ev }
  in
  log_t (lazy (fsprintf "t_subst before:@\n  %a@\n" pp_se se));
  log_t (lazy (fsprintf "t_subst after:@\n  %a@\n" pp_se new_se));
  t_conv true new_se ju

let t_let_unfold p ju =
  let se = ju.ju_se in
  match get_se_ctxt se p with
  | GLet(vs,e), sec ->
    let subst a = e_replace (mk_V vs) e a in
    let sec = { sec with
                sec_right = map_gdef_exp subst sec.sec_right;
                sec_ev = subst sec.sec_ev }
    in
    t_conv false (set_se_ctxt [] sec) ju
  | _ -> tacerror "rlet_unfold: no let at given position"
