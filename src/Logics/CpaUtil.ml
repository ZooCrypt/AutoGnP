open Type
open Expr
open Util

include CpaPretty

module F = Format

(* map functions *)

let rec map_expr_ce f ev = match ev with
  | Guess     -> Guess
  | Ask(h,e)  -> Ask(h, f e)
  | Eq(e1,e2) -> Eq(f e1, f e2)
  | Conj(evs) -> Conj(List.map (map_expr_ce f) evs)

let map_expr_cj f {cj_cipher; cj_ev} =
  {cj_cipher = f cj_cipher; cj_ev = map_expr_ce f cj_ev}

let map_expr_rl g rl =
  match rl with
  | CpaOpt(r,e)     -> CpaOpt(r, g e)
  | CpaFail1(h,e,r) -> CpaFail1(h, g e, r)
  | CpaFail2(h,e,r) -> CpaFail2(h, g e, r)
  | _            -> rl

let rec map_expr_cp g prf =
  { cp_rl = map_expr_rl g prf.cp_rl;
    cp_judgement = map_expr_cj g prf.cp_judgement;
    cp_prems = List.map (map_expr_cp g) prf.cp_prems }

(* iter functions *)

let rec iter_expr_ce g ev = match ev with
  | Guess     -> ()
  | Ask(_h,e)  -> g e
  | Eq(e1,e2) -> g e1; g e2
  | Conj(evs) -> List.iter (iter_expr_ce g) evs

let iter_expr_cj g {cj_cipher; cj_ev} =
  g cj_cipher;
  iter_expr_ce g cj_ev

let iter_expr_rl g rl =
  match rl with
  | CpaOpt(_,e) | CpaFail1(_,e,_) | CpaFail2(_,e,_) -> g e
  | _ -> ()

let rec iter_expr_cp g prf =
  iter_expr_rl g prf.cp_rl;
  iter_expr_cj g prf.cp_judgement;
  List.iter (iter_expr_cp g) prf.cp_prems

let find_expr_ce p ev =
  let res = ref None in
  iter_expr_ce (fun e -> try res := Some (e_find p e) with Not_found -> ()) ev; !res

let find_expr_cj p ev =
  let res = ref None in
  iter_expr_cj (fun e -> try res := Some (e_find p e) with Not_found -> ()) ev; !res

(* Extracting all identifiers included in expressions/../proofs *)

type ident =
    ITyvar of Tyvar.id
  | IIdent of Id.id

module Si = Set.Make(struct type t = ident let compare = Pervasives.compare end)

let si_unions sis = List.fold_left (fun si1 si2 -> Si.union si1 si2) Si.empty sis

let list_of_si si = Si.fold (fun x l -> x :: l) si []

module Mstring = Map.Make(struct type t = string let compare = Pervasives.compare end)

module Mnt = Map.Make(struct type t = (string * int) let compare = Pervasives.compare end)

let idents_ty ty =
  List.fold_left (fun acc tv -> Si.add (ITyvar tv) acc) Si.empty ty.ty_sum

let idents_rsym rsym = Si.add (IIdent rsym.Rsym.id) (idents_ty rsym.Rsym.ty)

let idents_psym psym = Si.add (IIdent psym.Psym.id) (idents_ty psym.Psym.dom)

let idents_hsym hsym =
  Si.add (IIdent hsym.Hsym.id)
         (Si.union (idents_ty hsym.Hsym.dom) (idents_ty hsym.Hsym.codom))

let idents_e e0 =
  let rec idents acc e =
    let acc' = Si.union (e_sub_fold idents acc e)
                        (idents_ty e.e_ty)
    in
    match e.e_node with
    | R rs               -> Si.union (idents_rsym rs) acc'
    | P(f,_) | Pinv(f,_) -> Si.union (idents_psym f)  acc'
    | H(h,_)             -> Si.union (idents_hsym h)  acc'
    | _                  -> acc'
  in idents Si.empty e0

let rec idents_ce ev = match ev with
  | Ask(_,e)  -> idents_e e
  | Eq(e1,e2) -> Si.union (idents_e e1) (idents_e e2)
  | Conj(evs) -> List.fold_left (fun acc ev -> Si.union acc (idents_ce ev)) Si.empty evs
  | Guess     -> Si.empty

let idents_cj {cj_cipher; cj_ev} =
  Si.union (idents_e cj_cipher) (idents_ce cj_ev)

let idents_rl rl =
  match rl with
  | CpaOpt(r,e)  -> Si.union (idents_rsym r) (idents_e e) 
  | CpaPerm(r,f) -> Si.union (idents_rsym r) (idents_psym f)
  | CpaMerge(r1,r2,r) | CpaSplit(r,r1,r2) -> 
      si_unions [ idents_rsym r1; idents_rsym r2; idents_rsym r]
  | CpaFail1(h,e,r) | CpaFail2(h,e,r) ->
      si_unions [idents_hsym h; idents_rsym r; idents_e e]
  | CpaRnd(r,c) | CpaEqs(c,r) ->
      Si.union (idents_rsym r) (idents_e c)
  | CpaOw(f,r1,tl,tm,r2s,c1,c2) ->
      si_unions ([ idents_e c1; idents_e c2; idents_ty tl;
                   idents_ty tm; idents_psym f; idents_rsym r1 ]
                 @(List.map idents_rsym r2s))
  | _ -> Si.empty

let rec idents_cp prf =
  si_unions ((List.map idents_cp prf.cp_prems)@
             [ idents_rl prf.cp_rl;
               idents_cj prf.cp_judgement ])

(* ----------------------------------------------------------------------- *)
(** {2 Exporting and Renaming} *)

(* Export *)

let rec export_ce (ev : cpaEvent) : ecpaEvent =
  match ev with
  | Guess     -> Guess
  | Ask(h,e)  -> Ask(Hsym.export h, e_export e)
  | Eq(e1,e2) -> Eq(e_export e1, e_export e2)
  | Conj(evs) -> Conj(List.map export_ce evs)

let export_cj {cj_cipher; cj_ev} =
  {cj_cipher = e_export cj_cipher; cj_ev = export_ce cj_ev}

let export_rl rl =
  let r_ex = Rsym.export in
  let e_ex = e_export in
  let p_ex = Psym.export in
  let h_ex = Hsym.export in
  let ty_ex = ty_export in
  match rl with
  | CpaOpt(r,e)                 -> CpaOpt(r_ex r, e_ex e)
  | CpaPerm(r,f)                -> CpaPerm(r_ex r, p_ex f)
  | CpaMerge(r1,r2,r)           -> CpaMerge(r_ex r1, r_ex r2, r_ex r)
  | CpaSplit(r,r1,r2)           -> CpaSplit(r_ex r, r_ex r1, r_ex r2)
  | CpaConj(i)                  -> CpaConj(i)
  | CpaNorm                     -> CpaNorm
  | CpaFail1(h,e,r)             -> CpaFail1(h_ex h, e_ex e, r_ex r)
  | CpaFail2(h,e,r)             -> CpaFail2(h_ex h, e_ex e, r_ex r)
  | CpaInd                      -> CpaInd
  | CpaRnd(r,c)                 -> CpaRnd(r_ex r,e_ex c)
  | CpaEqs(c,r)                 -> CpaEqs(e_ex c, r_ex r)
  | CpaAdmit                    -> CpaAdmit
  | CpaOw(f,r1,tl,tm,r2s,c1,c2) ->
      CpaOw(p_ex f, r_ex r1, ty_ex tl, ty_ex tm, List.map r_ex r2s, e_ex c1, e_ex c2)

let rec export_cp prf =
  { cp_rl = export_rl prf.cp_rl;
    cp_judgement = export_cj prf.cp_judgement;
    cp_prems = List.map export_cp prf.cp_prems}


let name_tag_of_ident i = match i with
  | ITyvar tyv -> (Tyvar.name tyv, Tyvar.tag tyv)
  | IIdent id  -> (Id.name id,  Id.tag id)

(* Building a map [m] from [(name,tag)] pairs of identifiers
   in a proof to [int]s such that [(name,m(name,tag))] is
   unique. Intuitively, for all names n, the first ident
   with name n gets 0, the second 1, and so on. *)
let binding_map (idents_x :'a -> Si.t) (x : 'a) : int Mnt.t =
  let name_tags = x |> idents_x
                    |> list_of_si
                    |> List.map name_tag_of_ident
                    |> List.sort (compare_on snd)
  in
  let nextMap = ref Mstring.empty in
  let getNext s =
    let tag = if Mstring.mem s !nextMap
              then Mstring.find s !nextMap else 0
  in nextMap := Mstring.add s (tag + 1) !nextMap;
       tag
  in
  let bindMap = ref Mnt.empty in
  let rec makeBmap nts = match nts with
    | [] -> !bindMap
    | (n,t)::nts ->
         begin
           if not (Mnt.mem (n,t) !bindMap) then (
             let tag = getNext n in
             bindMap := Mnt.add (n,t) tag !bindMap
           );
           makeBmap nts
         end
  in makeBmap name_tags

(* [map_eident_t g_tv g_id t] maps the functions [g_tv] and [g_id]
    over all occurences of type variables and idents in [t] *)
let map_eident_ty g_tv _g_id ty = (* keep _g_id for uniformity *)
  mk_ety (List.map g_tv ty.ty_sum)

let map_eident_rsym g_tv g_id rsym =
  let id' = g_id rsym.Rsym.id in
  let ty' = map_eident_ty g_tv g_id rsym.Rsym.ty in
  Rsym.mke (Id.name id') (Id.tag id') ty'

let map_eident_psym g_tv g_id psym =
  let id' = g_id psym.Psym.id in
  let dom' = map_eident_ty g_tv g_id psym.Psym.dom in
  Psym.mke (Id.name id') (Id.tag id') dom'

let map_eident_hsym g_tv g_id hsym =
  let id' = g_id hsym.Hsym.id in
  let dom' = map_eident_ty g_tv g_id hsym.Hsym.dom in
  let codom' = map_eident_ty g_tv g_id hsym.Hsym.codom in
  Hsym.mke (Id.name id') (Id.tag id') dom' codom'

let rec map_eident_e g_tv g_id e0 =
   let go    = map_eident_e g_tv g_id in
   let go_ty = map_eident_ty   g_tv g_id in
   let go_r  = map_eident_rsym g_tv g_id in
   let go_p  = map_eident_psym g_tv g_id in
   let go_h  = map_eident_hsym g_tv g_id in
   let e = match e0.e_node with
     | R v       -> R (go_r v)
     | P(f,a)    -> P(go_p f, go a)
     | Pinv(f,a) -> Pinv(go_p f,go a)
     | H(h,a)    -> H(go_h h,go a)
     | Xor(a,b)  -> Xor(go a, go b)
     | App es    -> App(List.map go es)
     | Proj((tyl,ty,tyr),a) ->
        let tyl', ty', tyr' = go_ty tyl, go_ty ty, go_ty tyr in
        Proj((tyl',ty',tyr'), go a)
     | Z | V _ -> e0.e_node
   in mk_ee e (go_ty e0.e_ty)

let rec map_eident_ce g_tv g_id ev =
  let go_exp = map_eident_e g_tv g_id in
  let go = map_eident_ce g_tv g_id in
  let go_h  = map_eident_hsym g_tv g_id in
  match ev with
  | Guess     -> Guess
  | Ask(h,e)  -> Ask(go_h h, go_exp e)
  | Eq(e1,e2) -> Eq(go_exp e1, go_exp e2)
  | Conj(evs) -> Conj(List.map go evs)

let map_eident_cj g_tv g_id {cj_cipher; cj_ev} =
  { cj_cipher = map_eident_e g_tv g_id cj_cipher;
    cj_ev = map_eident_ce g_tv g_id cj_ev }

let map_eident_rl g_tv g_id rl =
  let go_exp = map_eident_e g_tv g_id in
  let go_ty = map_eident_ty g_tv g_id in
  let go_r = map_eident_rsym g_tv g_id in
  let go_h = map_eident_hsym g_tv g_id in
  let go_p = map_eident_psym g_tv g_id in
  match rl with
  | CpaOpt(r,e)       -> CpaOpt(go_r r, go_exp e)
  | CpaPerm(r,f)      -> CpaPerm(go_r r, go_p f)
  | CpaMerge(r1,r2,r) -> CpaMerge(go_r r1, go_r r2, go_r r)
  | CpaSplit(r,r1,r2) -> CpaSplit(go_r r, go_r r1, go_r r2)
  | CpaFail1(h,e,r)   -> CpaFail1(go_h h, go_exp e, go_r r)
  | CpaFail2(h,e,r)   -> CpaFail2(go_h h, go_exp e, go_r r)
  | CpaEqs(c,r)       -> CpaEqs(go_exp c, go_r r)
  | CpaRnd(r,c)       -> CpaRnd(go_r r, go_exp c)
  | CpaOw(f,r1,tl,tm,r2s,c1,c2) ->
      CpaOw(go_p f, go_r r1, go_ty tl, go_ty tm, List.map go_r r2s, go_exp c1, go_exp c2)
  | CpaAdmit | CpaConj(_) | CpaNorm | CpaInd -> rl

let rec map_eident_cp g_tv g_id prf =
  { cp_rl = map_eident_rl g_tv g_id prf.cp_rl;
    cp_judgement = map_eident_cj g_tv g_id prf.cp_judgement;
    cp_prems = List.map (map_eident_cp g_tv g_id) prf.cp_prems }

(* Rename the proof such that all tags of idents are
   unique in combination with names. If names are already
   unique on their own, this means all tags will be 0. *)
let rename idents_x export_x map_eident_x x0 =
  let bmap = binding_map idents_x x0 in
  let x = export_x x0 in
  let g_tv tv =
    let name = Tyvar.name tv in
    let tag = Tyvar.tag tv in
    Tyvar.mke name (Mnt.find (name,tag) bmap)
  in
  let g_id id =
    let name = Id.name id in
    let tag = Id.tag id in
    Id.mke name (Mnt.find (name,tag) bmap)
  in map_eident_x g_tv g_id x

let rename_cp = rename idents_cp export_cp map_eident_cp
let rename_e = rename idents_e e_export map_eident_e
let rename_ty = rename idents_ty ty_export map_eident_ty

let pp_e fmt e = pp_exp fmt (rename_e e)

let typeError_to_string_rn (ty1,ty2,e1,me2,_s) =
  match me2 with
  | Some e2 -> 
      format_to_string (fun fmt ->
        F.fprintf fmt "incompatible types `%a' vs. `%a' for expressions `%a' and `%a'"
          pp_ty (rename_ty ty1) pp_ty (rename_ty ty2) pp_exp (rename_e e1) pp_exp (rename_e e2))
  | None ->
      format_to_string (fun fmt ->
        F.fprintf fmt "expected type `%a', got  `%a' for expressions `%a'"
          pp_ty (rename_ty ty1) pp_ty (rename_ty ty2) pp_exp (rename_e e1))


