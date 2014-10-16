open Ctypes
open Foreign
open IntPoly
open Util

module US = Unsigned.Size_t
module UL = Unsigned.ULong
module L  = List

let cexpvecs = ptr (ptr long)
let ccoeffs  = ptr long


(* ------------------------------------------------------------------------ *)
(* Function bindings *)

let c_print_cpoly =
  foreign "wrap_print" (int @-> int @-> cexpvecs @-> ccoeffs @-> returning void)

let c_new_expvecs =
  foreign "wrap_new_expvecs" (int @-> int @-> returning cexpvecs)

let c_free_expvecs =
  foreign "wrap_free_expvecs" (cexpvecs @-> int @-> returning void)

let c_new_coeffs = foreign "wrap_new_coeffs" (int @-> returning ccoeffs)

let c_free_coeffs = foreign "wrap_free_coeffs" (ccoeffs @-> returning void)

let c_gcd = foreign "wrap_gcd" (int @->
                                int @-> cexpvecs @-> ccoeffs @->
                                int @-> cexpvecs @-> ccoeffs @->
                                ptr cexpvecs @-> ptr ccoeffs @-> returning int)

(* ------------------------------------------------------------------------ *)
(* Conversions *)

let print_cpoly (nvars,nterms,cexpvecs,ccoeffs) =
  c_print_cpoly nvars nterms cexpvecs ccoeffs

let ipoly_to_cpoly ip =
  let nvars =
    match L.sort compare (IP.vars ip) with
    | []   -> 0
    | x::_ -> x + 1
  in
  let terms = IP.to_terms ip in
  let nterms = L.length terms in
  let ccoeffs = c_new_coeffs nterms in
  let cexpvecs = c_new_expvecs nvars nterms in
  L.iteri (fun i (evec,coeff) ->
    ccoeffs +@ i <-@ Signed.Long.of_int64 (Big_int.int64_of_big_int coeff);
    let cexpvec = !@ (cexpvecs +@ i) in
    for j = 0 to nvars - 1 do
      let e = try L.assoc j evec with Not_found -> 0 in
      cexpvec +@ j <-@ Signed.Long.of_int e
    done)
    terms;
  (nvars, nterms, cexpvecs, ccoeffs)

let cpoly_to_ipoly (nvars, nterms, cexpvecs, ccoeffs) =
  let res = ref [] in
  for i = 0 to nterms - 1 do
    let c = !@ (ccoeffs +@ i) in
    let cexpvec = !@ (cexpvecs +@ i) in
    let vs = ref [] in
    for j = 0 to nvars - 1 do
      let e = !@ (cexpvec +@ j) in
      vs := (j,Signed.Long.to_int e)::!vs;
    done;
    res := (!vs,Big_int.big_int_of_int64 (Signed.Long.to_int64 c))::!res;
  done;
  IP.from_terms !res

let free_cpoly (_nvars, nt, cevs, cos) =
  c_free_coeffs cos;
  c_free_expvecs cevs nt

let gcd p1 p2 =
  let (nvars1, nt1, cevs1, cos1) = ipoly_to_cpoly p1 in
  let (nvars2, nt2, cevs2, cos2) = ipoly_to_cpoly p2 in
  let nvars = max nvars1 nvars2 in
  let cevs_res = allocate cexpvecs (from_voidp (ptr long) null) in
  let cos_res = allocate ccoeffs (from_voidp long null) in
  let nt_res = c_gcd nvars nt1 cevs1 cos1 nt2 cevs2 cos2 cevs_res cos_res in
  let pres = cpoly_to_ipoly (nvars,nt_res,!@ cevs_res,!@ cos_res) in
  print_cpoly (nvars, nt_res, !@ cevs_res, !@ cos_res);
  free_cpoly (nvars, nt_res, !@ cevs_res, !@ cos_res);
  free_cpoly (nvars1, nt1, cevs1, cos1);
  free_cpoly (nvars2, nt2, cevs2, cos2);
  pres

(* ------------------------------------------------------------------------ *)
(* Testing *)

let () =
  let v1 = IP.var 1 in
  let p1 = IP.( v1 *@ v1 -@ (from_int 4) ) in
  let p2 = IP.( v1  +@ (from_int 2) ) in
  for _i = 1 to 1 do
    let p3 = gcd p1 p2 in
    F.printf "p1 = %a, p2 = %a, gcd = %a%!\n\n" IP.pp p1 IP.pp p2 IP.pp p3
  done

let _test () =
  let v1 = IP.var 1 in
  let p1 = IP.( v1 *@ v1 -@ (from_int 4) ) in
  let p2 = IP.( v1  +@ (from_int 2) ) in
  let ip1 = (ipoly_to_cpoly p1) in
  print_cpoly ip1;
  print_newline ();
  let p1 = cpoly_to_ipoly ip1 in
  F.printf "p1 = %a, p2 = %a%!\n\n" IP.pp p1 IP.pp p2;

  let cevs1 = c_new_expvecs 3 4 in
  let cos1 = c_new_coeffs 4 in
  c_print_cpoly 3 4 cevs1 cos1;
  print_newline ();
  let cevs2 = c_new_expvecs 3 2 in
  let cos2 = c_new_coeffs 2 in
  c_print_cpoly 3 2 cevs2 cos2;
  let cevs_res = allocate cexpvecs (from_voidp (ptr long) null) in
  let cos_res = allocate ccoeffs (from_voidp long null) in
  let nt_res = c_gcd 3 4 cevs1 cos1 2 cevs2 cos2 cevs_res cos_res in
  print_int nt_res;
  c_print_cpoly 3 nt_res (!@cevs_res) (!@cos_res);
  print_newline ()
