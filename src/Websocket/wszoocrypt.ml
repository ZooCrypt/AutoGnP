open Websocket
open Util
open Tactic
open ParserUtil

let (>>=) = Lwt.bind
let (<?>) a b = Lwt.choose [a;b]
let (<&>) a b = Lwt.join [a;b]

let theory_string = ref ""

(* FIXME: use map or hashtable
   We use the reversed list of commands (without '.')
   as the key for the corresponding proofstate.
*)
let ps_list = ref []

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

let processFrame frame =
  let l = (Util.split (Frame.content frame) '.') |> List.rev |> List.tl in
  let (ps, rem_cmds) = find_ps l in
  Lwt_io.printl ("received: ``"^Frame.content frame^"''") >>= fun () -> 
  Lwt_io.printl ("executing "^string_of_int (List.length rem_cmds)^" remaining commands") >>= fun () ->
  let res =
    try (let ps = List.fold_left
                    (fun ps cmd ->
                       handle_instr ps (Parse.instruction (cmd ^ ".")))
                    ps rem_cmds
         in
         ps_list := (l,ps)::!ps_list;
         fsprintf "@[<v>current goal:@\n%a@."
           pp_goals (Util.map_opt (Util.take 1) ps.ps_goals)
          |> fsget)
    with Parse.ParseError s -> "parse error: "^s 
  in
  Lwt.return (Frame.of_string res)

let server sockaddr =
  let rec echo_fun uri (stream, push) =
    Lwt_stream.next stream >>= fun frame ->
    processFrame frame >>= fun frame' ->
    Lwt.wrap (fun () -> push (Some frame')) >>= fun () ->
    echo_fun uri (stream, push) in
  establish_server sockaddr echo_fun

let rec wait_forever () =
  Lwt_unix.sleep 1000.0 >>= wait_forever

let _ =
  let run_server node service =
    Lwt_io_ext.sockaddr_of_dns node service >>= fun sa ->
    Lwt.return (server sa)
  in
  let main () = run_server "localhost" "9999" >>= fun _ -> wait_forever ()
  in
  Lwt_main.run (main ())
