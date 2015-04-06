(*s Infrastructure for defining derived rules. *)

(*i*)
open Nondet
open Abbrevs
open Util
open Syms
open Type
open Expr
open ExprUtils
open Game
open Assumption
open CoreTypes
open CoreRules

module Ht = Hashtbl
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Operators for tacticals} *)

let ( @> ) = t_seq

let ( @>> ) = t_seq_list

let ( @>>= ) = t_bind

let ( @>= ) = t_bind_ignore

let ( @| ) = t_or

let (@||) t1 t2 ju =
  let pss = t1 ju in
  match pull pss with (* try to preserve error from first call *)
  | Left (Some s) -> mplus (t2 ju) (mfail s)
  | Left None -> t2 ju
  | Right(_) -> pss

let rec t_seq_fold = function
  | []    -> t_id
  | t::ts -> t @> t_seq_fold ts

let rec t_or_fold = function
  | []    -> t_id
  | t::ts -> t @| t_or_fold ts

let t_print log s ju =
  log (lazy (fsprintf "%s:@\n%a" s pp_ju ju));
  t_id ju

let t_debug log s g =
  log (lazy s);
  t_id g

let t_guard f ju =
  if f ju then t_id ju else mempty

(*i ----------------------------------------------------------------------- i*)
(* \hd{Extracting samplings, lets, and guards from game} *)

(*i*)
let pp_samp fmt (i,(vs,d)) =
  F.fprintf fmt "%i: %a from %a" i Vsym.pp vs pp_distr d

let pp_osamp fmt ((i,j,k),(vs,d)) =
  F.fprintf fmt "(%i,%i,%i): %a from %a" i j k Vsym.pp vs pp_distr d

let pp_let fmt (i,(vs,e)) =
  F.fprintf fmt "%i: %a = %a" i Vsym.pp vs pp_exp e
(*i*)

let samplings gd =
  let samp i = function
    | GSamp(vs,(t,e)) -> Some (i,(vs,(t,e)))
    | _               -> None
  in
  cat_Some (L.mapi samp gd)

let osamplings gd =
  let lcmds_samplings gpos opos lcmds =
    let samp i = function
    | LSamp(vs,(t,e)) -> Some ((gpos,opos,i),(vs,(t,e)))
    | _              -> None
    in
    cat_Some (L.mapi samp lcmds)
  in
  let samp i = function
    | GCall(_,_,_,odefs) ->
      L.concat (L.mapi (fun opos (_,_,lcmds,_,_) -> lcmds_samplings i opos lcmds) odefs)
    | _ -> []
  in
  L.concat (L.mapi samp gd)

let oguards gd =
  let lcmds_guards gpos opos lcmds =
    let samp i = function
    | LGuard(e) -> Some ((gpos,opos,i),e)
    | _              -> None
    in
    cat_Some (L.mapi samp lcmds)
  in
  let samp i = function
    | GCall(_,_,_,odefs) ->
      L.concat (L.mapi (fun opos (_,_,lcmds,_,_) -> lcmds_guards i opos lcmds) odefs)
    | _ -> []
  in
  L.concat (L.mapi samp gd)

let lets gd =
  let get_let i = function
    | GLet(vs,e) -> Some (i,(vs,e))
    | _          -> None
  in
  cat_Some (L.mapi get_let gd)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Swap maximum amount forward and backward} *)

let rec parallel_swaps old_new_pos =
  let upd_pos op np p =
    (* op .. p .. np, if p = np before then p moves one to the right *)
    if op < np && op < p && p <= np then p - 1
    (* np .. p .. op, if p = np before then p moves one to the left *)
    else if np < op && np <= p && p < op then p + 1
    else p
  in
  match old_new_pos with
  | [] -> []
  | (op,np)::old_new_pos ->
    (op,np - op)::parallel_swaps (L.map (fun (op',np') -> (upd_pos op np op',np')) old_new_pos)

type dir = ToFront | ToEnd

let vars_dexc rv es = e_vars (mk_Tuple ((mk_V rv)::es))

let swap_max dir i se vs =
  let step = if dir=ToEnd then 1 else -1 in
  let rec aux j =
    if i+j < L.length se.se_gdef && 0 <= i+j then (
      let gcmd = get_se_gcmd se (i+j) in
      let cmd_vars = Se.union (write_gcmd gcmd) (read_gcmd gcmd) in
      if not (Se.is_empty (Se.inter vs cmd_vars)) then j - step else aux (j+step)
    ) else (
      j - step
    )
  in
  aux step

let t_swap_max dir i vs ju =
  let se = ju.ju_se in
  let offset = swap_max dir i se vs in
  let swap_samp =
    if offset = 0
    then t_id
    else t_swap i offset
  in
  swap_samp ju >>= fun ps -> ret (i+offset,ps)

let t_swap_others_max dir i ju =
  let se = ju.ju_se in
  let samps = samplings se.se_gdef in
  let samp_others =
    filter_map
      (fun (j,(rv,(ty,es))) ->
        if ((j > i && dir=ToFront) || (j < i && dir=ToEnd)) && ty_equal ty mk_Fq
        then Some (j,(rv,vars_dexc rv es)) else None)
      samps
  in
  let samp_others =
    (* when pushing forwards, we start with the last sampling to keep indices valid *)
    if dir=ToEnd then L.sort (fun a b -> - (compare (fst a) (fst b))) samp_others
    else samp_others
  in
  let rec aux i samp_others =
    match samp_others with
    | [] ->
      (fun ju ->
        t_id ju >>= fun ps ->
        ret (i,ps))
    | (j,(_rv,vs))::samp_others ->
      (fun ju ->
        t_swap_max dir j vs ju >>= fun (j',ps) ->
        let i' =
          if (j > i && j' <= i) then i + 1
          else if (j < i && j' >= i) then i - 1
          else i
        in
        ret (i', ps)
      ) @>>= fun i -> aux i samp_others
  in
  aux i samp_others ju

(*i ----------------------------------------------------------------------- i*)
(* \hd{Simplification and pretty printing} *)

(*i*)
let pp_rule ?hide_admit:(hide_admit=false) fmt ru =
  match ru with
  | Rconv ->
    F.fprintf fmt "rconv"
  | Rdist_eq ->
    F.fprintf fmt "dist_eq"
  | Rdist_sym ->
    F.fprintf fmt "dist_sym"
  | Rhybrid ->
    F.fprintf fmt "hybrid"
  | Rswap_main _ ->
    F.fprintf fmt "swap_main"
  | Rswap(pos,delta) ->
    F.fprintf fmt "swap %i %i" pos delta
  | Rexc(pos,es) ->
    F.fprintf fmt "except %i %a" pos (pp_list "," pp_exp) es
  | Rrnd(pos,vs,_,(v2,c2)) ->
    F.fprintf fmt "rnd %i %a@[<v>  %a -> %a@]" pos Vsym.pp vs Vsym.pp v2 pp_exp c2
  | Rrw_orcl((i,j,k),_dir) ->
    F.fprintf fmt "rw_orcl (%i,%i,%i)" i j k
  | Rswap_orcl((i,j,k),_i) ->
    F.fprintf fmt "swap_orcl (%i,%i,%i)" i j k
  | Rrnd_orcl((i,j,k),_c1,_c2)      ->
    F.fprintf fmt "rnd_orcl (%i,%i,%i)" i j k
  | Rexc_orcl((i,j,k),_es)          ->
    F.fprintf fmt "exc_orcl (%i,%i,%i)" i j k
  | Radd_test((i,j,k),e,_ads,_vss) ->
    F.fprintf fmt "add_test (%i,%i,%i) (%a)" i j k pp_exp e
  | Rcase_ev(_,e)   ->
    F.fprintf fmt "case @[<v 2>%a@]" pp_exp e
  | Rbad(_pos,_vs) ->
    F.fprintf fmt "bad"
  | Rctxt_ev(_i,_c) ->
    F.fprintf fmt "ctxt"
  | Rremove_ev(is) ->
    F.fprintf fmt "remove [%a]" (pp_list "," pp_int) is
  | Rmerge_ev(_i,_j) ->
    F.fprintf fmt "merge"
  | Rsplit_ev(i) ->
    F.fprintf fmt "split %i" i
  | Rrw_ev(i,_dir) ->
    F.fprintf fmt "rw_ev %i" i
  | Rassm_dec(_rngs,_dir,_ren,assm) ->
    F.fprintf fmt "assm_dec(%s)" assm.ad_name
  | Rassm_comp(_,_ren,assm) ->
    F.fprintf fmt "assm_comp(%s)" assm.ac_name
  | Radmit _ ->
    if not hide_admit then F.fprintf fmt "radmit"
  | Rfalse_ev ->
    F.fprintf fmt "false_ev"
  | Rrnd_indep(b,i) ->
    F.fprintf fmt "rnd_indep %b %i" b i

let rec pp_proof_tree_verbose ?hide_admit:(hide_admit=false) fmt pt =
  F.fprintf fmt
    ("##########################@\n%a@\n##########################@\n"^^
     "apply %a@\n"^^
     "  @[<v 0>%a@\n@]%!")
    pp_ju pt.pt_ju
    (pp_rule ~hide_admit) pt.pt_rule
    (pp_list "@\n" (pp_proof_tree_verbose ~hide_admit)) pt.pt_children

let pp_proof_tree_non_verbose ?hide_admit:(hide_admit=false) fmt pt =
  let rec aux n pt =
    F.fprintf fmt "@[%s@[<v 0>%a@]@]@\n%!" (String.make n ' ')
      (pp_rule ~hide_admit) pt.pt_rule;
    List.iter (aux (n + 2)) pt.pt_children
  in
  aux 0 pt

let pp_proof_tree ?hide_admit:(hide_admit=false) verbose =
  if verbose then pp_proof_tree_verbose ~hide_admit
  else pp_proof_tree_non_verbose ~hide_admit
(*i*)
  
let rec simplify_proof_tree pt =
  let children = L.map simplify_proof_tree pt.pt_children in
  let pt = pt_replace_children pt children in
  match pt.pt_rule, pt.pt_children with
  | Rconv,[pt1] ->
    begin match pt1.pt_rule, pt1.pt_children with
    | Rconv,[pt11] ->
      (* skip intermediate judgment *)
      let pss = t_conv true pt11.pt_ju.ju_se pt.pt_ju in
      let ps = Nondet.first pss in
      ps.validation [pt11]
    | _ -> 
      pt
    end
  | _ -> pt

let rec prove_by_admit s ps =
  if ps.subgoals = [] then
    ps
  else
    let ps = Nondet.first (apply_first (t_admit s) ps) in
    prove_by_admit s ps

let rec diff_proof_tree (pt1,pt2) =
  let is_Radmin ru = match ru with Radmit _ -> true | _ -> false in
  match pt1.pt_rule, pt2.pt_rule with
  | Radmit _, ru2 when not (is_Radmin ru2)  ->
    [ pt2 ]
  | _ ->
    conc_map diff_proof_tree (L.combine pt1.pt_children pt2.pt_children)

