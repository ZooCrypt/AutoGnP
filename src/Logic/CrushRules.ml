(*i*)
open Util
open Rules
open RewriteRules
open AssumptionRules
open RandomRules

module CR = CoreRules
module Ht = Hashtbl
(*i*)

let tn_fix finish depth t =
  let rec aux d =
    if d > 0 then
      t @> aux (d -1)
    else
      (if finish then CR.t_fail "hit bound" else CR.t_id)
  in
  aux depth

let tn_crush finish mi ts ju =
  let i = from_opt 5 mi in
  let step =
    (CR.t_cut ((t_norm ~fail_eq:true) @| CR.t_id))
    @> (   t_random_indep
        @| t_assm_dec ts None (Some LeftToRight) None
        @| t_rnd_maybe ts None None None)
  in
  t_or_list (L.map (fun j -> tn_fix finish j step) (list_from_to 1 (i+1))) ju
