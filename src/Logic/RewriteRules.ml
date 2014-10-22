(*s Derived tactics for rewriting. *)

(*i*)
open Game
open CoreRules
open Expr
open Norm
open NormField
open Util

module Ht = Hashtbl
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Derived rewriting tactics} *)

(** Unfold all lets and norm. *)
let t_norm ?fail_eq:(fe=false) ju =
  let new_ju = norm_ju ~norm:norm_expr_def ju in
  if fe && ju_equal ju new_ju
  then t_fail "t_norm: equal judgments" ju
  else t_conv true new_ju ju

(** Unfold all lets and norm, also remove tuple projection. *)
let t_norm_tuple_proj ju = 
  let norm e = remove_tuple_proj (norm_expr_def e) in
  let new_ju = norm_ju ~norm ju in
  t_conv true new_ju ju

(** Norm without unfolding. *)
let t_norm_nounfold ju = 
  let new_ju = map_ju_exp norm_expr_def ju in
  t_conv true new_ju ju


(** Unfold without norm. *)
let t_unfold_only ju = 
  let new_ju = norm_ju ~norm:(fun x -> x) ju in
  t_conv false new_ju ju

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

(*i norm and try to rewrite all exponentiations as products of
   (g^i)^o or X where i might be unknown, but o is not unknown.
   If there is a "let z=g^i" we can replace g^i by z in the next
   step. i*)
let t_norm_unknown unknown ju =
  let norm e = abbrev_ggen (rewrite_exps (se_of_list unknown) (norm_expr e)) in
  let new_ju = map_ju_exp norm ju in
  (* this is too restrictive, maybe we should give the allowed contexts?
  let unknown_se = se_of_list unknown in
  let check_unknown e0 =
    let rec aux ok_ctxt (e : expr) =
      if ok_ctxt || not (Se.mem e unknown_se) then (
        match e.e_node with
        | V(_) | Cnst(_) -> ()
        | H(_,e) | Proj(_,e) -> aux false e
        | App(GExp(_),[e1;e2]) when is_GGen e1 ->
          aux true e2
        | Tuple(es) | App(_,es) | Nary(_,es) ->
          L.iter (aux false) es
        | Exists(e1,e2,_) ->
          aux false e1; aux false e2
      ) else (
        tacerror "unknown value %a still occurs in forbidden contexts:@\n  %a@\n" pp_exp e pp_exp e0
      )
    in aux false e0
  in
  iter_ju_exp ~iexc:false check_unknown new_ju; *)
  t_conv true new_ju ju

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
        F.eprintf "@[@\n@\nbefore: %a@\n after: res :%a@\n e' %a@\n%!@]" pp_exp e pp_exp res pp_exp e';
        e'
  in
  e_map_ty_maximal Type.mk_Fq (solve a) e

(*i normalize field expressions (in exponents and elsewhere such that polynomials are
    expressed as a*f + g i*)
let t_norm_solve a ju =
  let norm e = abbrev_ggen (rewrite_div_reduce (norm_expr a) (norm_expr e)) in
  let new_ju = map_ju_exp norm ju in
  t_conv true new_ju ju

let t_let_abstract p vs e ju =
  let l,r = Util.cut_n p ju.ju_gdef in
  let v = mk_V vs in
  (*c could also try to normalize given expression *)
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
