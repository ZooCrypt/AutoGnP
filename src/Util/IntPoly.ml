open Poly
open Util

(* \ic{We use ints as variables here.} *)
module IP = MakePoly(
  struct
    type t = int
    let pp fmt i =F.fprintf fmt "v_%i" i
    let equal = (=)
    let compare = compare
  end) (IntRing)
