(*s Polynomial instances. *)

(*i*)
open Poly
open Abbrevs
open Util
(*i*)

(* \ic{Define a module of polynomials with integer coefficients and string variables.} *)
module SP = MakePoly(
  struct
    type t = string
    let pp = pp_string
    let equal = (=)
    let compare = compare
  end) (IntRing)

(* \ic{Define a module of polynomials with integer coefficients and integer variables.} *)
module IP = MakePoly(
  struct
    type t = int
    let pp fmt i =F.fprintf fmt "v_%i" i
    let equal = (=)
    let compare = compare
  end) (IntRing)
