open Websocket
open Util
open Tactic
open ParserUtil

module YS = Yojson.Safe
module F = Format

let (>>=) = Lwt.bind

(* We use the reversed list of commands (without '.')
   as the key for the corresponding proofstate. *)
let ps_list = ref []

let ps_file = ref ""
let disallow_save = ref false
let server_name = ref "localhost"

(* 'find_ps cmds' searches for the longest suffix of
   cmds for which there is a proofstate. The proofstate
   is returned together with the list of unhandled
   commands. *)
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

(* ----------------------------------------------------------------------- *)
(** {Handlers for different commands} *)

let process_unknown s =
  Lwt_io.printl ("unknown command: ``"^s^"''") >>= fun () ->
  Lwt.return (Frame.of_string "Unknown command")

let process_save content =
  Lwt_io.printl ("Save: ``"^content^"''") >>= fun () ->
  (* FIXME: use LWT *)
  if (Sys.file_exists !ps_file && not !disallow_save) then (
    output_file !ps_file content;
    Lwt.return (Frame.of_string (YS.to_string (`Assoc [("cmd", `String "saveOK")])))
  ) else (
    Lwt.return (Frame.of_string (YS.to_string (`Assoc [("cmd", `String "saveFAILED")])))
  )

let process_load () =
  Lwt_io.printl "Loading" >>= fun () ->
  (* FIXME: use Lwt *)
  let s = if Sys.file_exists !ps_file
          then input_file !ps_file
          else "(* Enter proof script below *)"
  in
  let res = `Assoc [("cmd", `String "setProof"); ("arg", `String s)] in
  Lwt.return (Frame.of_string (YS.to_string res))

let process_eval proofscript = 
  let l = (Util.splitn proofscript '.') |> List.rev |> List.tl in
  let (ps, rem_cmds) = find_ps l in
  Lwt_io.printl ("Eval: ``"^proofscript^"''") >>= fun () -> 
  Lwt_io.printl ("executing "^string_of_int (List.length rem_cmds)^" remaining commands") >>= fun () ->
  let res =
    (* FIXME: handle errors better, still return the handled prefix *)
    try (let ps = List.fold_left
                    (fun ps cmd ->
                       handle_instr ps (Parse.instruction (cmd ^ ".")))
                    ps rem_cmds
         in
         ps_list := (l,ps)::!ps_list;
         let g = match ps.ps_goals with
                 | None    -> "No proof started"
                 | Some [] -> "No goals"
                 | Some gs ->
                   fsprintf "@[%a@.%s@]"
                     pp_goals (Util.map_opt (Util.take 1) ps.ps_goals)
                     (let rem = List.length gs - 1 in if rem = 0 then "" else
                      string_of_int rem^" other goals")
                   |> fsget
         in `Assoc [("cmd", `String "setGoal"); ("arg", `String g)])
    with Parse.ParseError s ->
           `Assoc [("cmd", `String "error"); ("arg", `String ("parse error: "^s))]
  in
  Lwt.return (Frame.of_string (YS.to_string res))

(* ----------------------------------------------------------------------- *)
(** {Frame processing and server setup} *)

let process_frame frame =
  let inp = Frame.content frame in
  Lwt_io.printl ("Command: ``"^inp^"''") >>= fun () -> 
  match YS.from_string inp with
  | `Assoc l ->
     (try
        (let get k = List.assoc k l in
         match get "cmd", get "arg" with
         | `String "eval", `String pscript -> process_eval pscript
         | `String "load",_                -> process_load ()
         | `String "save", `String fcont   -> process_save fcont
         | _                               -> process_unknown inp)
      with Not_found -> process_unknown inp)
  | _ -> process_unknown inp

let run_server node service =
  let rec zoocrypt_serve uri (stream, push) =
    Lwt_stream.next stream >>= fun frame ->
    process_frame frame >>= fun frame' ->
    Lwt.wrap (fun () -> push (Some frame')) >>= fun () ->
    zoocrypt_serve uri (stream, push)
  in
  Lwt_io_ext.sockaddr_of_dns node service >>= fun sa ->
  Lwt.return (establish_server sa zoocrypt_serve)

let rec wait_forever () =
  Lwt_unix.sleep 1000.0 >>= wait_forever

(* ----------------------------------------------------------------------- *)
(** {Argument handling} *)

let main =
  let speclist =
    Arg.align
      [ ("-nosave", Arg.Set disallow_save, " disallow to save file");
        ("-s", Arg.Set_string server_name, " bind to this servername (default: localhost)")]
  in
  let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " <file>" in
  let parse_args s = if !ps_file = "" then ps_file := s else failwith "can only serve one file" in
  Arg.parse speclist parse_args usage_msg;
  if !ps_file = "" then (Arg.usage speclist usage_msg; exit 1);

  (* start server *)
  print_endline "Open the following URL in your browser (websocket support required):\n";
  print_endline ("    file://"^Sys.getcwd ()^"/web/index.html\n\n");
  if Sys.file_exists !ps_file
    then print_endline ("File: " ^ !ps_file)
    else failwith (F.sprintf "File ``%s'' does not exist." !ps_file);
  Lwt_main.run (run_server !server_name "9999" >>= fun _ -> wait_forever ())
