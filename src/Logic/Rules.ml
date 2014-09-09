(*s Infrastructure for defining derived rules. *)

(*i*)
open Nondet
open Util
open Syms
open Type
open Expr
open Game
open Assumption
open CoreRules

module Ht = Hashtbl
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Operators for tacticals} *)

let ( @> ) = t_seq

let ( @>>= ) = t_bind

let ( @>= ) = t_bind_ignore

(* let ( @+) t ts g = t_subgoal ts (t g) *)

let ( @| ) = t_or

let mk_name () = "x."^string_of_int (unique_int ())

let samplings gd =
  let samp i = function
    | GSamp(vs,(t,e)) -> Some (i,(vs,(t,e)))
    | _              -> None
  in
  cat_Some (L.mapi samp gd)

let pp_samp fmt (i,(vs,d)) =
  F.fprintf fmt "%i: %a from %a" i Vsym.pp vs pp_distr d

let lets gd =
  let get_let i = function
    | GLet(vs,e) -> Some (i,(vs,e))
    | _          -> None
  in
  cat_Some (L.mapi get_let gd)

let pp_let fmt (i,(vs,e)) =
  F.fprintf fmt "%i: %a = %a" i Vsym.pp vs pp_exp e

let rec t_seq_list = function
  | []    -> t_id
  | t::ts -> t @> t_seq_list ts

let rec t_or_list = function
  | []    -> t_id
  | t::ts -> t @| t_or_list ts

let t_print s ju =
  eprintf "%s:@\n%a@\n%!" s pp_ju ju;
  t_id ju

let t_debug s g =
  eprintf "%s" s;
  t_id g

let t_guard f ju =
  if f ju then t_id ju else mempty

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Swap maximum amount forward and backward} *)

type dir = ToFront | ToEnd

let swap_max dir i ju rv =
  let step = if dir=ToEnd then 1 else -1 in
  let rec aux j =
    if i+j < L.length ju.ju_gdef && 0 <= i+j then (
      let gcmd = get_ju_gcmd ju (i+j) in
      if Vsym.S.mem rv (gcmd_all_vars gcmd) then j - step else aux (j+step)
    ) else (
      j - step
    )
  in
  aux step

let t_swap_max dir i rv ju =
  let offset = swap_max dir i ju rv in
  let swap_samp =
    if offset = 0
    then t_id
    else t_swap i offset
  in
  eprintf "swap offset %i from %i\n" offset i;
  swap_samp ju >>= fun ps -> ret (i+offset,ps)

let t_swap_others_max dir i ju =
  let samps = samplings ju.ju_gdef in
  eprintf "samp_others: %a\n"
    (pp_list ", " (pp_pair pp_int Vsym.pp)) (L.map (fun (i,(v,_)) -> (i,v)) samps);
  let samp_others =
    L.map
      (fun (j,(rv,(ty,_))) ->
        if ((j > i && dir=ToFront) || (j < i && dir=ToEnd)) && ty_equal ty mk_Fq
        then Some (j,rv) else None)
      samps
    |> cat_Some
  in
  let samp_others =
    (* when pushing forwards, we start with the last sampling to keep indices valid *)
    if dir=ToEnd then L.sort (fun a b -> compare (fst a) (fst b)) samp_others
    else samp_others
  in
  let rec aux i samps =
    match samps with
    | [] ->
      (fun ju ->
        (* eprintf "swap others done %i\n%!" i; *)
        t_id ju >>= fun ps ->
        ret (i,ps))
    | (j,rv)::samps ->
      (fun ju ->
        t_swap_max dir j rv ju >>= fun (j',ps) ->
        let i' =
          if (j > i && j' < i) then i + 1
          else if (j < i && j' > i) then i - 1
          else i
        in
        eprintf "swap_other step done j=%i j'=%i i=%i i'=%i\n%!" j j' i i';
        ret (i', ps)
      ) @>>= fun i -> aux i samps
  in
  aux i samp_others ju

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Simplification and pretty printing} *)

let pp_rule fmt ru =
  let s = 
    match ru with
    | Rconv -> "rconv"
    | Rswap(_pos,_i) -> "rswap"
    | Rrnd(_pos,_c1,_c2) -> "rrnd"
    | Rexc(_pos,_es) -> "rexc"
    | Rrw_orcl(_opos,_dir) -> "rrw_orcl"
    | Rswap_orcl(_opos,_i) -> "rswap_orcl"
    | Rrnd_orcl(_opos,_c1,_c2) -> "rrnd_orcl"
    | Rexc_orcl(_opos,_es) -> "rexc_orcl"
    | Rcase_ev(_e) -> "rcase"
    | Radd_test(_opos,_e,_ads,_vss) -> "radd_test"
    | Rbad(_pos,_vs) -> "rbad"
    | Rctxt_ev(_i,_c) -> "rctxt"
    | Rremove_ev(_is) -> "rremove"
    | Rmerge_ev(_i,_j) -> "rmerge"
    | Rsplit_ev(_i) -> "rsplit"
    | Rrw_ev(_i,_dir) -> "rrw_ev"
    | Rassm_dec(_dir,_ren,assm) -> fsprintf "rassm_dec(%s)" assm.ad_name
    | Rassm_comp(_e,_ren,assm) -> fsprintf "rassm_comp(%s)" assm.ac_name
    | Radmit -> "radmit"
    | Rfalse_ev -> "rfalse_ev"
    | Rrnd_indep(_b,_i) -> "rrnd_indep"
  in
  F.fprintf fmt "%s" s

let rec pp_proof_tree fmt pt =
  F.fprintf fmt
    ("##########################@\n%a@\n##########################@\n"^^
     "apply %a@\n"^^
     "  @[<v 0>%a@\n@]")
    pp_ju pt.pt_ju
    pp_rule pt.pt_rule
    (pp_list "@\n" pp_proof_tree) pt.pt_children
  
let rec simplify_proof_tree pt =
  let children = L.map simplify_proof_tree pt.pt_children in
  let pt = pt_replace_children pt children in
  match pt.pt_rule, pt.pt_children with
  | Rconv,[pt1] ->
    begin match pt1.pt_rule, pt1.pt_children with
    | Rconv,[pt11] ->
      (* skip intermediate judgment *)
      let pss = t_conv true pt11.pt_ju pt.pt_ju in
      let ps = Nondet.first pss in
      ps.validation [pt11]
    | _ -> 
      pt
    end
  | _ -> pt

let rec prove_by_admit ps =
  if ps.subgoals = [] then
    ps.validation []
  else
    let ps = Nondet.first (apply_first t_admit ps) in
    prove_by_admit ps

