open Expr
open Cpa
open Util
open Type

module L = List

(* ----------------------------------------------------------------------- *)
(** {1 info about applicable rules} *)

type applicableInfo = {
  ai_ind              : bool;
  ai_msg_occ          : bool;
  ai_nf               : bool;
  ai_conjs            : int list;
  ai_rvars            : Rsym.t list;
  ai_rvars_xor        : (Rsym.t * expr) list;
  ai_rvars_non_basic  : Rsym.t list;
  ai_hashes           : Hsym.t list;
  ai_rvars_event_only : Rsym.t list;
  ai_perms_rvars      : (Psym.t * Rsym.t * Rsym.t list) list;
  ai_queried_msgs     : expr list
}

let true_no_exn cond =
  try  cond ()
  with _ -> true

let get_perms_rvars_cj j =
  let rvars = rvars_cj j in
  let ps = ref Se.empty in
  iter_expr_cj (fun e -> let es = e_find_all is_P e in
                         ps := Se.union !ps es) j;
  Se.fold (fun (e : expr) acc ->
             match e.e_node with
             | P(ps,e') when is_R e' ->
                 (ps, destr_R e',
                  L.map destr_R (Se.elements (Se.diff rvars (Se.singleton e'))))::acc
             | _ -> acc) !ps []

let get_rvars_xor_cj j =
  let xors = ref Se.empty in
  iter_expr_cj (fun e -> let es = e_find_all is_Xor e in
                         xors := Se.union !xors es) j;
  Se.fold (fun (e : expr) acc ->
             match e.e_node with
             | Xor(a,b) ->
                 (if is_R a then [destr_R a, b] else [])@
                 (if is_R b then [destr_R b, a] else [])@
                 acc
             | _ -> acc) !xors []

let get_hashes_cj j =
  let hs = ref Se.empty in
  iter_expr_cj (fun e -> let es = e_find_all is_H e in
                         hs := Se.union !hs es) j;
  Se.fold (fun (e : expr) (hs : Hsym.S.t) ->
             Hsym.S.add (fst (destr_H e)) hs) !hs Hsym.S.empty

let compute_ai j =
  let ind =
    (j.cj_ev = Guess) && not (true_no_exn (fun () -> find_expr_cj is_Msg j <> None))
  in
  let msg_occ = true_no_exn (fun () -> find_expr_cj is_Msg j <> None) in
  let nf = true_no_exn (fun () -> j = cjAt [0] (appNorm j)) in
  let conjs = list_from_to 0 (match j.cj_ev with Conj evs -> List.length evs | _ -> -1) in
  let hashes = Hsym.S.elements (get_hashes_cj j) in
  let rvars_event_only =
    List.map destr_R (Se.elements (Se.diff (rvars_ce j.cj_ev) (e_rvars j.cj_cipher)))
  in
  let rsym_non_basic rs = L.length rs.Rsym.ty.ty_sum > 1 in
  { ai_nf = nf;
    ai_ind = ind;
    ai_msg_occ = msg_occ;
    ai_conjs = conjs;
    ai_rvars = L.map destr_R (Se.elements (rvars_cj j));
    ai_rvars_xor = get_rvars_xor_cj j;
    ai_rvars_non_basic = L.filter rsym_non_basic (L.map destr_R (Se.elements (rvars_cj j)));
    ai_hashes = hashes;
    ai_rvars_event_only = rvars_event_only;
    ai_perms_rvars = if j.cj_ev <> Guess then get_perms_rvars_cj j else [];
    ai_queried_msgs = askEventMessages j.cj_ev
  }

