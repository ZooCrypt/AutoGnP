module PU = ParserUtil

let eval_theory s =
  let pt = Parse.theory s in
  List.fold_left (fun ps i -> PU.handle_instr ps i) PU.mk_ps pt

let main =
  if Array.length Sys.argv <> 2 then
    output_string stderr "usage: zoocrypt <inputfile>"
  else
    let szc = Util.input_file Sys.argv.(1) in
    ignore (eval_theory szc)
