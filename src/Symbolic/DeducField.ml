(*s Deducibility for fields *)

(*i*)
open CAS
open Norm
(*i*)

let solve_fq ecs e =
  let ecs = List.map (fun (c,e) -> (c, norm_expr e)) ecs in
  norm_expr (solve_fq_sage ecs e)
