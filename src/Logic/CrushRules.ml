(*i*)
open Util
open Rules
open RewriteRules
open AssumptionRules
open RandomRules

module CR = CoreRules
module Ht = Hashtbl
(*i*)

let tn_fix depth t =
  let rec aux d =
    if d > 0 then
      CR.t_ensure_progress t  @> aux (d -1)
    else
      CR.t_id
  in
  aux depth

let tn_crush mi ts =
  let i = from_opt 5 mi in
  let step =
    (CR.t_cut ((t_norm ~fail_eq:true) @| CR.t_id))
    @> (   t_random_indep
        @| t_assm_dec ts None (Some LeftToRight) None
        @| t_rnd_maybe ts None None None)
  in
  tn_fix i step
