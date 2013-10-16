open Game
open CoreRule

(* unfold all lets and norm *)
let rnorm ju = 
  let new_ju = norm_ju ~norm:norm_expr_def ju in
  rconv new_ju ju

(* norm without unfolding *)
let rnorm_nounfold ju = 
  let new_ju = map_ju_exp norm_expr_def ju in
  rconv new_ju ju

(* unfold without norm *)
let runfold_only ju = 
  let new_ju = norm_ju ~norm:(fun x -> x) ju in
  rconv new_ju ju

