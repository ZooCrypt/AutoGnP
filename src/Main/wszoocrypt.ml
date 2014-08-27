open Websocket
open Util
open Tactic
open CoreRules
open TheoryState

module YS = Yojson.Safe
module PU = ParserUtil

let (>>=) = Lwt.bind

let ps_file = ref ""
let disallow_save = ref false
let server_name = ref "localhost"

(* ----------------------------------------------------------------------- *)
(** {Proofstate cache} *)

(* We use the reversed list of commands (without '.')
   as the key for the corresponding theory state. *)
let ts_cache = Hashtbl.create 10

(* 'lookup_ps_cache cmds' searches for the longest suffix of
   cmds for which there is a proofstate. The proofstate
   is returned together with the list of unhandled
   commands. *)
let lookup_ts_cache cmds =
  let rec go handled_cmds rem_cmds =
    try
      (Hashtbl.find ts_cache handled_cmds, List.rev handled_cmds, rem_cmds)
    with
      Not_found ->
        (match handled_cmds with
         | [] -> ((mk_ts (), []), List.rev handled_cmds, rem_cmds)
         | last::before -> go before (last::rem_cmds))
  in go (List.rev cmds) []

let insert_ts_cache cmds (ts,msgs) =
  Hashtbl.add ts_cache (List.rev cmds) (ts,msgs)

(* ----------------------------------------------------------------------- *)
(** {Handlers for different commands} *)

let process_unknown s =
  F.printf "unknown command: %s\n%!" s;
  Lwt.return (Frame.of_string "Unknown command")

let process_save content =
  F.printf "Save: %s\n%!" content;
  Lwt.return (
    if (Sys.file_exists !ps_file && not !disallow_save) then (
      output_file !ps_file content;
      Frame.of_string (YS.to_string (`Assoc [("cmd", `String "saveOK")]))
    ) else (
      Frame.of_string (YS.to_string (`Assoc [("cmd", `String "saveFAILED")]))
    )
  )

let process_load () =
  F.printf "Loading %s\n%!" !ps_file;
  let s = if Sys.file_exists !ps_file then input_file !ps_file
          else "(* Enter proof script below *)"
  in
  let res = `Assoc [("cmd", `String "setProof"); ("arg", `String s)] in
  Lwt.return (Frame.of_string (YS.to_string res))

let split_proof_script s =
  let rec find_dot i =
    try
      match s.[i] with
      | '.' ->
        Some i
      | '"' ->
        find_dot (find_quote (i+1))
      | '(' when s.[i+1] = '*' ->
        find_dot (find_comment_end (i+2))
      | _ ->
        find_dot (i+1)
    with
      Invalid_argument _ -> None
  and find_comment_end i =
    match s.[i] with
    | '*' when s.[i+1] = ')' -> i+2
    | _ -> find_comment_end (i+1)
  and find_quote i =
    match s.[i] with
    | '"' -> i+1
    | _   -> find_quote (i+1)
  in
  let rec go i acc =
    match find_dot i with
    | Some j -> go (j+1) ((String.sub s i (j - i))::acc)
    | None   -> List.rev acc
  in
  go 0 []

let process_eval proofscript =
  let l = split_proof_script proofscript in
  (* F.printf "Eval: ``%a''\n%!" (pp_list ";" pp_string) l; *)
  let ((ts0, msgs0), handled_cmds, rem_cmds) = lookup_ts_cache l in
  (* F.printf "Eval: ``%s''\n%!" proofscript; *)
  F.printf "executing %i remaining commands\n%!" (List.length rem_cmds);
  let rhandled = ref handled_cmds in
  let rts = ref ts0 in
  let rmsgs = ref msgs0 in
  (* handle the remaining commands, return the last message if ok
     and the error and the position up to where processing was
     successfull otherwise *)
  let ok_upto () =
    List.fold_left (fun acc l -> acc + 1 + String.length l) 0 !rhandled
  in
  let res =
    let error =
      let last_cmd = ref "" in
      try 
        List.iter
          (fun cmd ->
             last_cmd := cmd;
             let (ts, msg) = handle_instr !rts (Parse.instruction (cmd ^ ".")) in
             rhandled := !rhandled @ [ cmd ]; rts := ts; rmsgs := !rmsgs @ [ msg ];
             insert_ts_cache !rhandled (ts,!rmsgs))
          rem_cmds;
          `Null
      with
        | PU.ParseError s ->
          `String (F.sprintf "parse error %s in ``%s''" s !last_cmd)
        | Invalid_rule s ->
          `String (F.sprintf "invalid rule application: %s" s)
        | Expr.TypeError  e ->
          `String (F.sprintf "type error: %s" (Expr.typeError_to_string e))
        | e ->
          `String (F.sprintf "unknown error: %s" (Printexc.to_string e))
    in
    let g =
      match !rts.ts_ps with
      | BeforeProof  -> "No proof started."
      | ClosedTheory -> "Theory closed."
      | ActiveProof { CoreRules.subgoals = [] } -> "No goals."
      | ActiveProof gs ->
        fsprintf "@[%a@.%s@]"
          pp_jus 
          (Util.take 1 gs.subgoals)
          (let rem = 
             List.length gs.CoreRules.subgoals - 1 in if rem = 0 then "" else
          string_of_int rem^" other goals")
    in `Assoc [ ("cmd", `String "setGoal");
                ("ok_upto", `Int (ok_upto ()));
                ("err", error);
                ("msgs", `List (List.map (fun s -> `String s) !rmsgs));
                ("arg", `String g) ]
  in
  Lwt.return (Frame.of_string (YS.to_string res))

(* ----------------------------------------------------------------------- *)
(** {Frame processing and server setup} *)

let process_frame frame =
  let inp = Frame.content frame in
  (* F.printf "Command: ``%s''\n%!" inp; *)
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
