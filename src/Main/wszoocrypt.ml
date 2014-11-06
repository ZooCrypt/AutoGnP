(*s Websocket server for web interface *)

(*i*)
open Websocket
open Util
open Abbrevs
open Tactic
open CoreRules
open TheoryTypes
open TheoryState

module YS = Yojson.Safe
module PU = ParserUtil
(*i*)

let (>>=) = Lwt.bind

let ps_file  = ref ""
let ps_files = ref []
let disallow_save = ref false
let server_name = ref "localhost"

(*i ----------------------------------------------------------------------- i*)
(* \hd{Proofstate cache} *)

(** We use the reversed list of commands (without '.')
    as the key for the corresponding theory state. *)
let ts_cache = Hashtbl.create 10

(** [lookup_ps_cache cmds] searches for the longest suffix of
    cmds for which there is a proofstate. The proofstate
    is returned together with the list of unhandled
    commands. *)
let lookup_ts_cache filename cmds =
  let rec go handled_cmds rem_cmds =
    try
      let fcache = Hashtbl.find ts_cache filename in
      (Hashtbl.find fcache handled_cmds, List.rev handled_cmds, rem_cmds)
    with
      Not_found ->
        (match handled_cmds with
         | [] -> ((mk_ts (), []), List.rev handled_cmds, rem_cmds)
         | last::before -> go before (last::rem_cmds))
  in go (List.rev cmds) []

let insert_ts_cache filename cmds (ts,msgs) =
  let fcache =
    try Hashtbl.find ts_cache filename
    with Not_found ->
      let fcache = Hashtbl.create 10 in
      Hashtbl.add ts_cache filename fcache;
      fcache
  in
  Hashtbl.add fcache (List.rev cmds) (ts,msgs)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Handlers for different commands} *)

let process_unknown s =
  F.printf "unknown command: %s\n%!" s;
  Lwt.return (Frame.of_string "Unknown command")

let process_list_files () =
  Lwt.return
    (Frame.of_string
       (YS.to_string (`Assoc [("cmd", `String "setFiles");
                              ("arg", `List (List.map (fun s -> `String s) !ps_files))])))

let process_save filename content =
  F.printf "Save %s: %s\n%!" filename content;
  assert (List.mem filename !ps_files);
  Lwt.return (
    if (Sys.file_exists !ps_file && not !disallow_save) then (
      output_file filename content;
      Frame.of_string (YS.to_string (`Assoc [("cmd", `String "saveOK")]))
    ) else (
      Frame.of_string (YS.to_string (`Assoc [("cmd", `String "saveFAILED")]))
    )
  )

let process_load s =
  Hashtbl.clear ts_cache;
  ps_file := if s = "" then !ps_file else s;
  F.printf "Loading %s\n%!" !ps_file;
  let s =
    if Sys.file_exists !ps_file && List.mem !ps_file !ps_files then input_file !ps_file
    else "(* Enter proof script below *)"
  in
  let res = `Assoc [("cmd", `String "setProof");
                    ("arg", `String s);
                    ("filename", `String !ps_file) ] in
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

let process_eval fname proofscript =
  (*i let buf = Util.set_debug_buffer () in i*)
  let l = split_proof_script proofscript in
  (*i F.printf "Eval: ``%a''\n%!" (pp_list ";" pp_string) l; i*)
  let ((ts0, msgs0), handled_cmds, rem_cmds) = lookup_ts_cache fname l in
  (*i F.printf "Eval: ``%s''\n%!" proofscript; i*)
  F.printf "executing %i remaining commands\n%!" (List.length rem_cmds);
  let rhandled = ref handled_cmds in
  let rts = ref ts0 in
  let rmsgs = ref msgs0 in
  (*c handle the remaining commands, return the last message if ok
      and the error and the position up to where processing was
      successful otherwise *)
  let ok_upto () =
    List.fold_left (fun acc l -> acc + 1 + String.length l) 0 !rhandled
  in
  let res =
    let error =
      let n_rem_cmds = ref (L.length rem_cmds) in
      let last_cmd = ref "" in
      try
        List.iter
          (fun cmd ->
             last_cmd := cmd; decr n_rem_cmds;
             let verb = !n_rem_cmds = 0 in
             let (ts, msg) = handle_instr verb !rts (Parse.instruction (cmd ^ ".")) in
             rhandled := !rhandled @ [ cmd ]; rts := ts; rmsgs := !rmsgs @ [ msg ];

             insert_ts_cache fname !rhandled (ts,!rmsgs))
          rem_cmds;
          `Null
      with
        | PU.ParseError s ->
          `String (F.sprintf "parse error %s in ``%s''" s !last_cmd)
        | Invalid_rule s ->
          `String (F.sprintf "invalid rule application: %s" s)
        | Expr.TypeError  e ->
          `String (F.sprintf "type error: %s" (ExprUtils.typeError_to_string e))
        | e ->
          `String (F.sprintf "unknown error: %s,\n%s"
                     (Printexc.to_string e)
                     (Printexc.get_backtrace ()))
    in
    let g =
      match !rts.ts_ps with
      | BeforeProof    -> "No proof started."
      | ClosedTheory _ -> "Theory closed."
      | ActiveProof ({ CoreRules.subgoals = [] },_,_,_) -> "No goals."
      | ActiveProof (gs,_,_,_) ->
        fsprintf "@[%a@.%s@]"
          (pp_jus 1)
          gs.subgoals
          (let rem =
             List.length gs.CoreRules.subgoals - 1 in if rem = 0 then "" else
          string_of_int rem^" other goals")
    in `Assoc [ ("cmd", `String "setGoal");
                ("ok_upto", `Int (ok_upto ()));
                ("debug", `String "" (*i (Buffer.contents buf) i*));
                ("err", error);
                ("msgs", `List (List.map (fun s -> `String s) !rmsgs));
                ("arg", `String g) ]
  in
  Lwt.return (Frame.of_string (YS.to_string res))

(*i ----------------------------------------------------------------------- i*)
(* \hd{Frame processing and server setup} *)

let process_frame frame =
  let inp = Frame.content frame in
  F.printf "Command: ``%s''\n%!" inp;
  match YS.from_string inp with
  | `Assoc l ->
     (try
        (let get k = List.assoc k l in
         match get "cmd", get "arg" with
         | `String cmd, `String arg when cmd = "eval" || cmd = "save" ->
           begin match get "filename" with
           | `String fname ->
             begin match cmd with
             | "eval" -> process_eval fname arg
             | "save" -> process_save fname arg
             | _ -> assert false
             end
           | _ -> process_unknown inp
           end
         | `String "load", `String fname   -> process_load fname
         | `String "listFiles", _          -> process_list_files ()
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

(*i ----------------------------------------------------------------------- i*)
(* \hd{Argument handling} *)

let main =
  Printexc.record_backtrace true;
  let speclist =
    Arg.align
      [ ("-nosave", Arg.Set disallow_save, " disallow to save file");
        ("-s", Arg.Set_string server_name, " bind to this servername (default: localhost)")]
  in
  let usage_msg = "Usage: " ^ Sys.argv.(0) ^ " <file>" in
  let parse_args s = ps_files := !ps_files @ [s] in
  Arg.parse speclist parse_args usage_msg;
  if !ps_files = [] then (Arg.usage speclist usage_msg; exit 1);
  ps_file := List.hd !ps_files;

  (* start server *)
  print_endline "Open the following URL in your browser (websocket support required):\n";
  print_endline ("    file://"^Sys.getcwd ()^"/web/index.html\n\n");
  if Sys.file_exists !ps_file
    then print_endline ("Files: " ^ (String.concat ", " !ps_files))
    else failwith (F.sprintf "File ``%s'' does not exist." !ps_file);
  Lwt_main.run (run_server !server_name "9999" >>= fun _ -> wait_forever ())
