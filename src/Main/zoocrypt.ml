open Tactic

let main =
  if Array.length Sys.argv <> 2 then
    output_string stderr "usage: zoocrypt <inputfile>"
  else
    let szc = Util.input_file Sys.argv.(1) in
    ignore (eval_theory szc)
