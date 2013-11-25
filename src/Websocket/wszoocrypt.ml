open Websocket
open Util
open Tactic
open ParserUtil

let (>>=) = Lwt.bind
let (<?>) a b = Lwt.choose [a;b]
let (<&>) a b = Lwt.join [a;b]

let theory_string = ref ""

let ps = ref (ParserUtil.mk_ps ())

let processFrame frame =
  Lwt_io.printl (Frame.content frame) >>= fun () -> 
  let i = Parse.instruction (Frame.content frame) in
  ps := Tactic.handle_instr !ps i;
  let res = fsprintf "@[<v>current goal:@\n%a@."
              pp_goals (Util.map_opt (Util.take 1) (!ps).ps_goals)
            |> fsget
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
