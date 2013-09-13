open Expr
open Util
open Type
open Norm

include CpaUtil

module P = Printf
module F = Format

let _ = F.pp_set_margin F.str_formatter 9999

(* ----------------------------------------------------------------------- *)
(** {1 Helper functions } *)

let mk_cp rl j prems = { cp_rl = rl; cp_judgement = j; cp_prems = prems }

let mk_cp_Admit rl j js = mk_cp rl j (List.map (fun jp -> mk_cp CpaAdmit jp []) js)

let find_hash_arg h j =
  let h_arg = ref None in
  let module E = struct exception Multiple end in
  let f e1 = match e1.e_node, !h_arg with
             | H(h2,e2), None when Hsym.equal h h2 ->
                 h_arg := Some e2
             | H(h2,e2), Some e3 when Hsym.equal h h2 & not (e_equal e2 e3) ->
                 raise E.Multiple
             | _ -> ()
  in
  try  iter_expr_cj (e_iter f) j; !h_arg
  with E.Multiple -> None

let find_msg j =
  let module E = struct exception Found of expr end in
  let f e1 =
    try  let m = e_find is_Msg e1 in raise (E.Found m)
    with Not_found -> ()
  in
  try
    iter_expr_cj f j; None
  with E.Found m -> Some m

let se_unions ses = List.fold_left (fun se1 se2 -> Se.union se1 se2) Se.empty ses

let rec rvars_ce ce = match ce with
  | Guess     -> Se.empty
  | Ask(_h,e) -> e_rvars e
  | Eq(e1,e2) -> Se.union (e_rvars e1) (e_rvars e2)
  | Conj(evs) -> se_unions (List.map rvars_ce evs)

let rvars_cj j = Se.union (e_rvars j.cj_cipher) (rvars_ce j.cj_ev)

let rvars_cp  cp =
  let rvs = ref Se.empty in
  iter_expr_cp (fun e -> rvs:= Se.union (e_rvars e) !rvs) cp;
  !rvs

exception AppFailure of cpaJudgement * string

let failApp j s = raise (AppFailure(j,s))

let ensureFresh j rule r =
  if (Se.mem (mk_R r) (rvars_cj j)) then
  failApp j (fsprintf
               "%s: random variable %a occurs in judgement"
               rule Rsym.pp r |> fsget)

let ensureContext j rule c =
  if not (Se.is_empty (e_rvars c)) then
  failApp j (fsprintf"%s: context %a contains random variables"
               rule pp_e c |> fsget)


let ensureDisjoint j rule e1 e2 =
  if (Se.inter (e_rvars e1) (e_rvars e2)) != Se.empty then
  failApp j (fsprintf
               "%s: the expressions %a and %a share random variables"
               rule pp_e e1 pp_e e2 |> fsget)

let ensureHashOnce j rule h =
  match find_hash_arg h j with
  | Some e -> e
  | None -> failApp j (rule ^ ": hash applied to fewer or more than one expressions")

let ensureNonZero j rule rv = 
  if is_ty_zero rv.Rsym.ty then failApp j (rule ^ ": random variable has length 0")

let askEventMessages ev =
  let rec getEvs evs =
    List.concat (List.map (function Conj(evs) -> getEvs evs | e -> [e]) evs)
  in
  List.concat (List.map (function Ask(_h,e) -> [e] | _ -> []) (getEvs [ev]))


(* ----------------------------------------------------------------------- *)
(** {2 Rules} *)

(* Bridging *)

let appNorm j = mk_cp_Admit CpaNorm j [map_expr_cj norm j]

let appConj i j = match j with
  | { cj_cipher = e; cj_ev = Conj evs } when i < List.length evs && List.length evs > 1->
      let ev' = match take i evs @ drop (i+1) evs with
                | [ev] -> ev
                | evs  -> Conj evs
      in mk_cp_Admit (CpaConj i) j [{cj_cipher = e; cj_ev = ev' }]
  | _ -> failApp j "conj: invalid index"

(* We replace [r] by [r + e]. The effect of the original rule in the
   paper that performs the opposite replacement can be achieved by
   combining [perm] and [norm]. *)
let appOpt r e j =
  ensureDisjoint j "opt" (mk_R r) e;
  let j' = map_expr_cj (e_replace (mk_R r) (mk_Xor (mk_R r) e)) j in
  mk_cp_Admit (CpaOpt(r,e)) j [j']

(* We replace [r] by [f^-1(r)]. *) 
let appPerm r f j =
  let j' = map_expr_cj (e_replace (mk_R r) (mk_Pinv f (mk_R r))) j in
  mk_cp_Admit (CpaPerm(r,f)) j [j']

let appSplit r r1 r2 j =
  ensureFresh j "split" r1;
  ensureFresh j "split" r2;
  ensureDisjoint j "split" (mk_R r1) (mk_R r2);
  let j' = map_expr_cj (e_replace (mk_R r) (mk_App [mk_R r1; mk_R r2])) j in
  mk_cp_Admit (CpaSplit(r,r1,r2)) j [j']

let appMerge r1 r2 r j =
  ensureFresh j "merge" r;
  ensureDisjoint j "merge" (mk_R r1) (mk_R r2);
  let r_first  = mk_Proj (mk_ty [], r1.Rsym.ty, r2.Rsym.ty) (mk_R r) in
  let r_second = mk_Proj (r1.Rsym.ty, r2.Rsym.ty, mk_ty []) (mk_R r) in
  let j' = map_expr_cj (fun e -> e |> e_replace (mk_R r1) r_first |> e_replace (mk_R r2) r_second) j
  in mk_cp_Admit (CpaMerge(r1,r2,r)) j [j']

(* Fail *)

let appFail1 h r j =
  ensureFresh j "fail1" r;
  let e = ensureHashOnce j "fail1" h in
  let j1 = map_expr_cj (e_replace (mk_H h e) (mk_R r)) j in
  mk_cp_Admit (CpaFail1(h,e,r)) j [j1; {j1 with cj_ev = Ask(h,e)} ]

let appFail2 h r j =
 let add_conj new_ev ev = match ev with
   | Conj(evs) -> Conj(evs@[new_ev])
   | ev1 -> Conj([ev1; new_ev])
  in
  ensureFresh j "fail2" r;
  let e = ensureHashOnce j "fail2" h in
  let j1 = map_expr_cj (e_replace (mk_H h e) (mk_R r)) j in
  let j2 = {j with cj_ev = add_conj (Ask(h,e)) j.cj_ev} in
  mk_cp_Admit (CpaFail2(h,e,r)) j [j1; j2]

(* Terminal *)

let appInd j =
  if j.cj_ev = Guess && not (e_exists is_Msg j.cj_cipher) then (
    mk_cp CpaInd j [] 
  ) else (
    failApp j "ind: msg still in ciphertext or not Guess event"
  )

let appRnd r c j =
  let fail s = failApp j (P.sprintf "rnd: %s" s) in
  ensureNonZero j "rnd" r;
  ensureContext j "ow" c;
  if e_exists (e_equal (mk_R r)) j.cj_cipher then (
    fail "random variable occurs in cipher"
  ) else (
    let qes = askEventMessages j.cj_ev in
    let ty = ty_concat_l (List.map (fun x -> x.e_ty) qes) in
    let c_res = norm (e_replace (mk_V Star ty) (mk_App qes) c) in
  	if e_equal c_res (mk_R r) then (
      mk_cp (CpaRnd(r,c)) j []
    ) else ( fail (fsprintf "invalid context: expected %a, got %a"
                     pp_e (mk_R r) pp_e c_res |> fsget)))


let appOw f r1v k l r2vs c1 c2 j =
  let fail s = failApp j (P.sprintf "ow: %s" s) in
  ensureContext j "ow" c1;
  ensureContext j "ow" c2;
  ensureNonZero j "ow" r1v;
  let r1 = mk_R r1v in
  let r2s = mk_App (List.map mk_R r2vs) in
  ensureDisjoint j "ow" r1 r2s;
  let qes = askEventMessages j.cj_ev in
  let qes_ty = ty_concat_l (List.map (fun x -> x.e_ty) qes) in
  let f_r1 = mk_P f r1 in
  let (msg_ty, m_msg) = match find_msg j with (* if the judgement does not include m_b *)
    | Some m -> (m.e_ty, [m])                 (* then we do not provide it in star1/star2 *)
    | None   -> (ty_concat_l [], [])
  in
  let star1 = mk_V Star (ty_concat_l [qes_ty; r2s.e_ty; msg_ty]) in
  let star2 = mk_V Star (ty_concat_l [f_r1.e_ty; r2s.e_ty; msg_ty]) in
  let rhs1 = mk_App (qes@[r2s]@m_msg) in
  let rhs2 = mk_App ([f_r1]@[r2s]@m_msg) in
  (* check that c1[e1,..,ek,r2,msg] =E [r1]_k^l and
	              c2[f(r1),r2,msg]    =E c* *)
  let c1_res = norm (e_replace star1 rhs1 c1) in
  let res1   = norm (mk_Proj2 (k,l) r1) in
  let c2_res = norm (e_replace star2 rhs2 c2) in
  let res2   = norm j.cj_cipher in
  P.eprintf "%s" (fsprintf "context c2: expected %a, got %a, " pp_e res2 pp_e c2_res |> fsget);
  if not (e_equal c1_res res1)
      then fail (fsprintf "invalid context c1: expected %a, got %a"
                   pp_e res1 pp_e c1_res |> fsget)
      else if not (e_equal c2_res res2)
      then fail (fsprintf "invalid context c2: expected %a, got %a"
                   pp_e res2 pp_e c2_res |> fsget)
      else mk_cp (CpaOw(f,r1v,k,l,r2vs,c1,c2)) j []

let appAdmit j = mk_cp CpaAdmit j []

(* ----------------------------------------------------------------------- *)
(** {3 Rule application} *)

type path = int list

exception InvalidPath of cpaProof * path * string
exception InvalidAdmit of cpaProof * int * string

let applyAt path0 tac prf0 =
  let rec go prf path =
    match prf.cp_rl, prf.cp_judgement, prf.cp_prems, path with
    | _,j,_, [] -> tac j
    | rl, j ,prems, i::path when i < List.length prems ->
        mk_cp rl j (take i prems @ [ go (List.nth prems i) path] @ drop (i+1) prems)
    | _ -> raise (InvalidPath(prf0, path0, "applyAt"))
  in go prf0 path0

let rec cpAt path0 prf = match path0 with
  | [] -> prf
  | i::path when i < List.length prf.cp_prems ->
      cpAt path (List.nth prf.cp_prems i)
  | _ -> raise (InvalidPath(prf, path0, "prfAt"))

let admitPaths prf =
  let rec add_idx i ys = match ys with
    | [] -> []
    | x::xs -> (i,x)::add_idx (i+1) xs
  in
  let rec find path p0 =
    match p0.cp_rl, p0.cp_prems with
    | CpaAdmit,_  -> [ path ]
    | _, prems -> List.concat (List.map (fun (i,p) -> find (path @ [i]) p) (add_idx 0 prems))
  in find [] prf

let cjAt path prf = (cpAt path prf).cp_judgement
