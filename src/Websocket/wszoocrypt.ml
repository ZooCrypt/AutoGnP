open Websocket
open Util
open Tactic
open ParserUtil

module YS = Yojson.Safe

let (>>=) = Lwt.bind
let (<?>) a b = Lwt.choose [a;b]
let (<&>) a b = Lwt.join [a;b]

let theory_string = ref ""

(* We use the reversed list of commands (without '.')
   as the key for the corresponding proofstate. *)
let ps_list = ref []

let ps_file = ref ""

let find_ps cmds =
  let rec go handled_cmds rem_cmds =
    try
      (List.assoc handled_cmds !ps_list, rem_cmds)
    with
      Not_found ->
        (match handled_cmds with
         | [] -> (ParserUtil.mk_ps (), rem_cmds)
         | last::before -> go before (last::rem_cmds))
  in go cmds []

let processUnknown s =
  Lwt_io.printl ("unknown command: ``"^s^"''") >>= fun () ->
  Lwt.return (Frame.of_string "Unknown command")

let processSave content =
  Lwt_io.printl ("Save: ``"^content^"''") >>= fun () ->
  if Sys.file_exists !ps_file then output_file !ps_file content else ();
  Lwt.return (Frame.of_string (YS.to_string (`Assoc [("cmd", `String "saveOK")])))

let processLoad () =
  Lwt_io.printl ("Loading") >>= fun () ->
  (* FIXME: use Lwt *)
  let s = if Sys.file_exists !ps_file
          then input_file !ps_file
          else "(* Enter proof script below *)"
  in
  let res = `Assoc [("cmd", `String "setProof"); ("arg", `String s)] in
  Lwt.return (Frame.of_string (YS.to_string res))

let processEval proofscript = 
  let l = (Util.splitn proofscript '.') |> List.rev |> List.tl in
  let (ps, rem_cmds) = find_ps l in
  Lwt_io.printl ("Eval: ``"^proofscript^"''") >>= fun () -> 
  Lwt_io.printl ("executing "^string_of_int (List.length rem_cmds)^" remaining commands") >>= fun () ->
  let res =
    try (let ps = List.fold_left
                    (fun ps cmd ->
                       handle_instr ps (Parse.instruction (cmd ^ ".")))
                    ps rem_cmds
         in
         ps_list := (l,ps)::!ps_list;
         let g = fsprintf "@[<v>current goal:@\n%a@."
                   pp_goals (Util.map_opt (Util.take 1) ps.ps_goals)
                   |> fsget
         in `Assoc [("cmd", `String "setGoal"); ("arg", `String g)])
    with Parse.ParseError s ->
           `Assoc [("cmd", `String "error"); ("arg", `String ("parse error: "^s))]
  in
  Lwt.return (Frame.of_string (YS.to_string res))

let processFrame frame =
  let inp = Frame.content frame in
  Lwt_io.printl ("Command: ``"^inp^"''") >>= fun () -> 
  match YS.from_string inp with
  | `Assoc l ->
     (try
        (let get k = List.assoc k l in
         match get "cmd", get "arg" with
         | `String "eval", `String pscript -> processEval pscript
         | `String "load",_                -> processLoad ()
         | `String "save", `String fcont   -> processSave fcont
         | _                               -> processUnknown inp)
      with Not_found -> processUnknown inp)
  | _ -> processUnknown inp

let run_server node service =
  let rec zoocrypt_serve uri (stream, push) =
    Lwt_stream.next stream >>= fun frame ->
    processFrame frame >>= fun frame' ->
    Lwt.wrap (fun () -> push (Some frame')) >>= fun () ->
    zoocrypt_serve uri (stream, push)
  in
  Lwt_io_ext.sockaddr_of_dns node service >>= fun sa ->
  Lwt.return (establish_server sa zoocrypt_serve)

let rec wait_forever () =
  Lwt_unix.sleep 1000.0 >>= wait_forever

let _ =
  let speclist = Arg.align [ ] in
  let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " <file>" in
  let parse_args s = if !ps_file = "" then ps_file := s else failwith "can only serve one file" in
  Arg.parse speclist parse_args usage_msg;
  if !ps_file = "" then (print_endline usage_msg; exit 1);
  print_endline "Open the following URL in your browser (websocket support required):\n";
  print_endline ("    file://"^Sys.getcwd ()^"/web/zoocrypt.html\n\n");
  (if Sys.file_exists !ps_file then Lwt_io.printl ("File: " ^ !ps_file) else Lwt.return ()) >>= fun _ ->  
  Lwt_main.run (run_server "localhost" "9999" >>= fun _ -> wait_forever ())
