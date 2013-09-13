(* FIXME: Convert to OUnit tests *)
open Expr
open Type
open Cpa

let () = Format.set_margin 500

(* We start with the CPA proof of OAEP from the long version:
   |r| = l, |m| = k, |0| = n
   G : l -> k+n
   H : k+n -> l
   f : k + n + l
   f((G(r)+(m||0))||H(G(r)+(m||0))+r)
*)

(* types *)
let l = mk_ty [Tyvar.mk "l"]
let k = mk_ty [Tyvar.mk "k"]
let n = mk_ty [Tyvar.mk "n"]
let k_n = ty_concat_l [k;n]
let k_n_l = ty_concat_l [k;n;l]

(* hash and permutation symbols, random var *)
let sG = Hsym.mk "G" l k_n
let sH = Hsym.mk "H" k_n l
let sf = Psym.mk "f" k_n_l
let rv = Rsym.mk "r" l

let (+.) a b = mk_Xor a b
let (|.) a b = mk_App [a;b]
let g a = mk_H sG a
let h a = mk_H sH a
let f a = mk_P sf a
let r = mk_R rv
let msg = mk_Msg k
let z_n = mk_Z n

let main () =
  Format.printf "\nProof:\n";
  let s = (g r) +. (msg |. z_n) in
  let t = (h s) +. r in
  let cstar = f (s |. t) in
  let j1 = {cj_cipher = cstar; cj_ev = Guess} in
  let p1 = mk_cp CpaAdmit j1 [] in
  Format.printf "@.@[%a@]@." pp_cp p1

let test_norm =
  let j1 = {cj_cipher = (msg |. z_n) +. (mk_Z k |. z_n) ; cj_ev = Guess} in
  Format.printf "@.@[%a@]@." pp_cp (appNorm j1)

let test_weaken =
  let j1 = {cj_cipher = (msg |. z_n) +. (mk_Z k |. z_n) ; cj_ev = Conj [Ask(sH,r); Ask(sH,z_n)]} in
  Format.printf "@.@[%a@]@." pp_cp (appConj 0 j1);
  Format.printf "@.@[%a@]@." pp_cp (appConj 1 j1);
  try Format.printf "@.@[%a@]@." pp_cp (appConj 2 j1) with _ -> ()

let test_norm =
  let j1 = {cj_cipher = r +. (h(mk_Z k_n)) ; cj_ev = Guess} in
  let p1 = appOpt rv (h(mk_Z k_n)) j1 in
  Format.printf "@.@[%a@]@." pp_cp p1;
  let p2 = applyAt [0] appNorm p1 in
  Format.printf "@.@[%a@]@." pp_cp p2

let test_perm =
  let r2v = Rsym.mk "r2" k_n_l in
  let r2 = mk_R r2v in
  let j1 = {cj_cipher = (r2 +. f(mk_Z k_n_l)) ; cj_ev = Guess} in
  let p1 = appPerm r2v sf j1 in
  Format.printf "@.@[%a@]@." pp_cp p1

let test_split =
  let r2v = Rsym.mk "r2" k_n_l in
  let r2 = mk_R r2v in
  let j1 = {cj_cipher = (r2 +. f(mk_Z k_n_l)) ; cj_ev = Guess} in
  let r3 = Rsym.mk "r3" k in
  let r4 = Rsym.mk "r4" (ty_concat n l) in
  let p1 = appSplit r2v r3 r4 j1 in
  Format.printf "@.@[%a@]@." pp_cp p1

let test_merge =
  let r2v = Rsym.mk "r2" k_n in
  let r2 = mk_R r2v in
  let j1 = {cj_cipher = r2 ; cj_ev = Guess} in
  let r3 = Rsym.mk "r3" k in
  let r4 = Rsym.mk "r4" n in
  let p1 = appSplit r2v r3 r4 j1 in
  Format.printf "@.@[%a@]@." pp_cp p1;
  match p1.cp_rl with
  | CpaSplit(_,r3,r4) ->
      let p2 = applyAt [0] (appMerge r3 r4 r2v) p1 in
      Format.printf "@.@[%a@]@." pp_cp p2;
      let p3 = applyAt [0; 0] appNorm p2 in
      Format.printf "@.@[%a@]@." pp_cp p3
  | _ -> ()

let test_fail1 =
  let s = (g r) +. (msg |. z_n) in
  let t = (h s) +. r in
  let cstar = f (s |. t) in
  let j1 = {cj_cipher = cstar; cj_ev = Guess} in
  let r2 = Rsym.mk "r2" k_n in
  let p1 = appFail1 sG r2 j1 in
  Format.printf "@.@[%a@]@." pp_cp p1

let test_fail1_2 =
  let s = (g r) +. (g (mk_Z l)) in
  let t = (h s) +. r in
  let cstar = f (s |. t) in
  let j1 = {cj_cipher = cstar; cj_ev = Guess} in
  let r2 = Rsym.mk "r2" k_n in
  try ignore (appFail1 sG r2 j1) with AppFailure _ -> ()

let test_fail2 =
  let s = (g r) +. (msg |. z_n) in
  let t = (h s) +. r in
  let cstar = f (s |. t) in
  let j1 = {cj_cipher = cstar; cj_ev = Guess} in
  let r2 = Rsym.mk "r2" k_n in
  let p1 = appFail2 sG r2 j1 in
  Format.printf "@.@[%a@]@." pp_cp p1

let test_rnd_1 =
  let r2v = Rsym.mk "r2" k_n in
  let r2 = mk_R r2v in
  let cstar = mk_Z k in
  let j1 = {cj_cipher = cstar; cj_ev = Ask(sH,r2)} in
  let p1 = appRnd r2v (mk_V Star k_n) j1 in
  Format.printf "@.@[%a@]@." pp_cp p1

let test_rnd_2 =
  let r2v = Rsym.mk "r2" k_n in
  let r2 = mk_R r2v in
  let j1 = {cj_cipher = h r2; cj_ev = Ask(sH,r2)} in
  try ignore (appRnd r2v (mk_V Star k_n) j1) with _ -> ()

let test_rnd_3 =
  let r2v = Rsym.mk "r2" k_n in
  let r2 = mk_R r2v in
  let j1 = {cj_cipher = mk_Z k_n; cj_ev = Ask(sH,h r2)} in
  try ignore (appRnd r2v (mk_V Star k_n) j1) with _ -> ()

let test_ow_1 =
  let r1v = Rsym.mk "r1" k_n_l in
  let r1 = mk_R r1v in
  let j1 = {cj_cipher = f r1; cj_ev = Ask(sH,mk_Proj (mk_ty [], k_n, l) r1)} in
  let star1 = mk_V Star k_n in
  let star2 = mk_V Star k_n_l in
  let p1 = appOw sf r1v (mk_ty []) k_n [] star1 star2 j1 in
  Format.printf "@.@[%a@]@." pp_cp p1

let test_ow_2 =
  let r1v = Rsym.mk "r1" k_n_l in
  let r1 = mk_R r1v in
  let j1 = {cj_cipher = f r1; cj_ev = Ask(sH,mk_Proj (mk_ty [], k_n, l) r1)} in
  let star1 = mk_V Star k_n in
  let star2 = mk_V Star (ty_concat k_n_l k_n) in
  try ignore (appOw sf r1v (mk_ty []) k_n [r1v] star1 star2 j1) with _ -> ()

let test_ow_3 =
  let r1v = Rsym.mk "r1" k_n_l in
  let r1 = mk_R r1v in
  let j1 = {cj_cipher = f r1; cj_ev = Ask(sH,mk_Proj (mk_ty [], k_n, l) r1)} in
  let star1 = (mk_V Star k_n) +. (g(mk_Z l)) in
  let star2 = mk_V Star k_n_l in
  try ignore (appOw sf r1v (mk_ty []) k_n [] star1 star2 j1) with _ -> ()

let test_rename_1 =
  let s = (g r) +. (msg |. z_n) in
  let t = (h s) +. r in
  let cstar = f (s |. t) in
  let j1 = {cj_cipher = cstar; cj_ev = Guess} in
  let r2 = Rsym.mk "r2" k_n in
  let p1 = appFail2 sG r2 j1 in
  Format.printf "@.@[%a@]@." pp_cp p1;
  let p2 = rename_cp p1 in
  Format.printf "@.@[%a@]@." pp_cp p2

let test_rename_2 =
  let s = (g r) +. (msg |. z_n) in
  let r_clash = Rsym.mk "r" l in
  let t = (h s) +. r +. (mk_R r_clash) in
  let cstar = f (s |. t) in
  let j1 = {cj_cipher = cstar; cj_ev = Guess} in
  let p1 = mk_cp CpaAdmit j1 [] in
  ()
  (*
  let bm = binding_map_cp p1 in
  let pp_pair fmt ((n,t),i) = Format.fprintf fmt "(%s,%i) -> %i" n t i in
  Format.printf "@.%a@." (pp_list "," pp_pair) (Mnt.bindings bm);
  let p2 = rename_cp p1 in
  Format.printf "@.@[%a@]@." pp_cp p2
  *)

(*
let test_appFirst_1 =
  let s = (g r) +. (msg |. z_n) in
  let t = (h s) +. r in
  let cstar = f (s |. t) in
  let j1 = {cj_cipher = cstar; cj_ev = Guess} in
  let r2 = Rsym.mk "r2" k_n in
  let p1 = appFail1 sG r2 j1 in
  Format.printf "@.@[%a@]@." pp_cp (applyFirst appNorm p1)
*)