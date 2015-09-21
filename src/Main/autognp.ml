(* * Simple batch proof processor with Emacs mode *)

open Tactic
open ExprUtils
open Abbrevs
open Util
open CoreRules
open TheoryTypes

module PT = ParserTools

let emacs_mode = ref false
let ps_files = ref []
let theory_states = ref [TheoryState.mk_ts ()]
  (* we will ensure that theory_states will be always non-empty *)
let ts_statenum () = L.length !theory_states - 1

let encode s = s
  (* BatString.nreplace ~str:s ~by:"\\<^newline>" ~sub:"\n" *)

let decode s =
  BatString.nreplace ~str:s ~sub:"\\<^newline>" ~by:"\n"

let eval_emacs () =
  let exec_instr cmd =
    let cmd = decode cmd in
    let (ts,msg) =
      if BatString.starts_with cmd "undo " then (
        let cur_statenum = ts_statenum () in
        let (_undo, next_statenum_s) = BatString.split ~by:" " cmd in
        let next_statenum =
          int_of_string (BatString.rchop ~n:1 next_statenum_s)
        in
        if cur_statenum < next_statenum then
          failwith "Invalid undo statenum.";
        let undo_n = cur_statenum - next_statenum in
        begin match BatList.drop undo_n !theory_states with
        | (ts::_) as tss ->
          theory_states := tss;
          (ts,"")
        | [] -> failwith "impossible"
        end
      ) else ( 
        let is = Parse.instruction cmd in
        let ts = L.hd !theory_states in
        let (ts,msg) =
          L.fold_left
            (fun (ts, msg) i ->
               let (ts', msg') = handle_instr true ts i in
               (ts', if msg = "" then msg' else msg'^"---\n"^msg))
            (ts,"")
            is
        in
        theory_states := ts::!theory_states;
        (ts,msg)
      )
    in
    let g =
      match ts.ts_ps with
      | BeforeProof    -> ""
      | ClosedTheory _ -> ""
      | ActiveProof ({ CoreRules.subgoals = [] },_,_,_) ->
        "Current goal:\nNo remaining goals."
      | ActiveProof (gs,_,_,_) ->
        fsprintf "@[Current goal:@\n%a@.%s@]"
          (pp_jus 1)
          gs.subgoals
          (let rem =
             List.length gs.CoreRules.subgoals - 1 in if rem = 0 then "" else
          string_of_int rem^" other goals")
    in
    (msg,g) 
  in
  let print_prompt () = F.printf "[%i]>\n%!" (ts_statenum ()) in
  print_prompt ();
  let outp s = print_endline (encode s) in
  while true do
    let s = read_line () in
    (try
       let (msg, g) = exec_instr s in
       print_endline msg;
       print_endline g
     with
       | PT.ParseError pe ->
         outp (fsprintf "[error-%i-%i]%s"
                 pe.PT.pe_char_start pe.PT.pe_char_end
                 (PT.error_string "<emacs>" pe))
       | Invalid_rule s ->
         outp (fsprintf "[error-0-3]invalid rule application: %s" s)
       | Expr.TypeError  e ->
         outp (fsprintf "[error-0-3]type error: %s"
                 (ExprUtils.typeError_to_string e))
       | e ->
         outp (fsprintf "[error-0-3]unknown error: %s,\n%s"
                 (Printexc.to_string e)
                 (Printexc.get_backtrace ()))
    );
    print_prompt ()
  done

let main =
  let speclist =
    Arg.align
      [ ("-emacs", Arg.Set emacs_mode,
         "use with Emacs") ]
  in
  let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " <file>" in
  let parse_args s = ps_files := !ps_files @ [s] in
  Arg.parse speclist parse_args usage_msg;
  if not !emacs_mode then (
    if !ps_files = [] then (
      prerr_endline "Input file required for non-emacs mode";
      exit (-1)
    );
    let szc = Util.input_file Sys.argv.(1) in
    ignore (catch_TypeError (fun () -> eval_theory szc))
  ) else (
    if !ps_files <> [] then (
      prerr_endline "Cannot give input files for emacs mode";
      exit (-1)
    );
    eval_emacs ()
  )
