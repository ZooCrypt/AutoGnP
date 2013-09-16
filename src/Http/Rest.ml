open LogicProve
open LogicParse
open LogicProofsearch
open Util
open Logic
open LogicBound

module ERef = Eliom_reference
module YS = Yojson.Safe
module F = Format
module P = Printf
module E = Expr
module S = String
module L = List

let _ = F.pp_set_margin F.str_formatter 9999

let (>>=) = Lwt.bind

(************************************************************************)
(** {1 Json handling}  *)

type reply =
    Ok of YS.json
  | Error of YS.json
  | InternalError of string 

exception JsonExtract of string

let reply_to_json rep = match rep with
  | Ok js           -> `Assoc [ ("res_type", `String "Ok");            ("res_val", js) ]
  | Error js        -> `Assoc [ ("res_type", `String "Error");         ("res_val", js) ]
  | InternalError s -> `Assoc [ ("res_type", `String "InternalError"); ("res_val", `String s) ]

let getString k l : string = match exc_to_opt (fun () -> List.assoc k l) with
  | Some (`String s) -> s
  | _                ->
      raise (JsonExtract (P.sprintf "getString for key `%s' from `%s' failed" k (YS.to_string (`Assoc l))))

let getInt k l : int = match exc_to_opt (fun () -> List.assoc k l) with
  | Some (`Int i) -> i
  | _             ->
      raise (JsonExtract (P.sprintf "getInt for key `%s' from `%s' failed" k (YS.to_string (`Assoc l))))

let getAssoc js : (string * YS.json) list = match js with
  | `Assoc al -> al
  | _         -> raise (JsonExtract (P.sprintf "getAssoc from `%s' failed" (YS.to_string js)))


let applicableInfo_to_json ai =
  `Assoc [ ("ind", `Bool ai.ai_ind);
           ("msg_occ", `Bool ai.ai_msg_occ);
           ("nf", `Bool ai.ai_nf);
           ("conjs", `List (L.map (fun i -> `Int i) ai.ai_conjs));
           ("rvars", `List (L.map (fun rs -> `String (Id.name rs.Rsym.id)) ai.ai_rvars));
           ("rvars_xor", `Assoc (L.map (fun (rs,e) ->
                                          (Id.name rs.Rsym.id, `String (fsprintf "%a" pp_e e |> fsget)))
                                       ai.ai_rvars_xor));
           ("rvars_non_basic", `List (L.map (fun rs -> `String (Id.name rs.Rsym.id)) ai.ai_rvars_non_basic));
           ("hashes", `List (L.map (fun rs -> `String (Id.name rs.Hsym.id)) ai.ai_hashes));
           ("rvars_event_only", `List (L.map (fun rs -> `String (Id.name rs.Rsym.id)) ai.ai_rvars_event_only));
           ("queried_msgs", `String (fsprintf "%a" pp_e (Norm.norm (E.mk_App ai.ai_queried_msgs)) |> fsget));
           ("perms_rvars",
            `List (L.map (fun (ps,rs,other_rs) ->
                            `Assoc [ ("perm", `String (Id.name ps.Psym.id));
                                     ("perm_ty", `List (L.map (fun id -> `String (Type.Tyvar.name id)) (ps.Psym.dom.Type.ty_sum)));
                                     ("rvar", `String (Id.name rs.Rsym.id));
                                     ("other_rvars", `String (String.concat "|" (L.map (fun rs -> Id.name rs.Rsym.id) other_rs)))
                                    ])
                  ai.ai_perms_rvars)) ]

let tscheme_to_json ts = `Assoc
  [ ("msg_decl",      `String ts.ts_msg_decl);
    ("hash_decls",    `String ts.ts_hash_decls);
    ("ts_perm_decls", `String ts.ts_perm_decls);
    ("ts_rvar_decls", `String ts.ts_rvar_decls);
    ("ts_cipher",     `String ts.ts_cipher) ]

let proofstate_to_json tps0 =
  let ps0 = ps_of_tps tps0 in
  let p = rename_cp ps0.ps_proof in
  let ju_to_json ju = `String (fsprintf "%a" pph_cj ju |> fsget) in
  let goals = ref [] in
  let goals_path = ref [] in
  let rec go path p =
    let prems =
      if p.cp_rl = CpaAdmit
      then (let i = List.length !goals in
            goals := !goals @ [ju_to_json p.cp_judgement];
            goals_path := !goals_path @ [path];
            [`Assoc [ ("judgement", `String (P.sprintf "&#x2207;<sub>%i</sub>" i));
                      ("prems", `List []) ]])
      else List.map2 (fun i p -> go (path@[i]) p) (list_from_to 0 (L.length p.cp_prems)) p.cp_prems
    in
    `Assoc [ ("prems", `List prems );
             ("rule", `String (fsprintf "%a" pp_cr p.cp_rl |> fsget));
             ("judgement", ju_to_json p.cp_judgement) ]

  in
  let p' = go [] p in (* NEED side-effects for !goals *)
  let get_ai path =
      applicableInfo_to_json (compute_ai (cjAt path ps0.ps_proof))
  in
  let first_fresh_rvar =
    let get_counter s =
      try
        if S.get s 0 = 'r'
        then [ int_of_string (String.sub s 1 (String.length s - 1)) ]
        else []
      with _ -> []
    in 
    let rvar_numbers =
      L.concat
        (L.map (fun e -> get_counter (Id.name ((E.destr_R e).Rsym.id)))
               (E.Se.elements (rvars_cp ps0.ps_proof)))
    in (L.fold_left max 0 rvar_numbers) + 1
  in
  `Assoc [ ("proof", `Assoc [ ("prems", `List [ p' ] ) ]);
           ("goals", `List !goals);
           ("bound", `String (fsprintf "%a" pp_prob (bound_of_proof false p) |> fsget));
           ("bound_spd", `String (fsprintf "%a" pp_prob (bound_of_proof true p) |> fsget));
           ("history", `String (String.concat "\n" ps0.ps_history));
           ("goals_ai", `List (L.map get_ai !goals_path));
           ("fresh_rvar", `Int first_fresh_rvar);
           ("tscheme", tscheme_to_json tps0.tps_scheme) ]

(************************************************************************)
(** {2 Server state} *)

let proofs_ref =
  ERef.eref ~scope:Eliom_common.site_scope
    ~persistent:"proofs-1"
    Mint.empty

let proofs_mutex = Lwt_mutex.create ()

let add_tproofState (tps : tproofState) =
  let add m =
    let new_key =
      if Mint.empty = m then 1
      else fst (Mint.max_binding m) + 1
    in
    (new_key, Mint.add new_key tps m)
  in
  Lwt_mutex.lock proofs_mutex >>= fun _ ->
  Lwt.finalize
    (fun () -> 
       ERef.get proofs_ref >>= fun m ->
       let (k,m') = add m in (* FIXME: handle exception *)
       ERef.set proofs_ref m' >>= fun _ ->
       Lwt.return k)
    (fun () -> Lwt.return (Lwt_mutex.unlock proofs_mutex))

let get_tproofState proofId : (tproofState option) Lwt.t =
  ERef.get proofs_ref >>= fun m ->
  let res =
    try
      Some (Mint.find proofId m)
    with Not_found -> None
  in 
  Lwt.return res

let get_proofState proofId =
  get_tproofState proofId >>= fun tps -> Lwt.return (map_opt ps_of_tps tps)

(************************************************************************)
(** {3 Json requests} *)

let parse_req cmd =
  try
    match YS.from_string cmd with
    | `Assoc l ->
        (let get k = List.assoc k l in
         let req_arg = get "req_arg" in
         match get "req_name" with
         | `String req_name ->
             Some (req_name, req_arg)
         | _ -> None)
    | _ -> None
  with _ -> None

let handle_start arg =
  Lwt.catch
    (fun () ->
     let l = getAssoc arg in
     let msg_decl   = getString "msg_decl" l in
     let rvar_decls = getString "rvar_decls" l in
     let hash_decls = getString "hash_decls" l in
     let perm_decls = getString "perm_decls" l in
     let cipher     = getString "cipher" l in
     let tps = { tps_scheme =
                   { ts_msg_decl = msg_decl;
                     ts_hash_decls = hash_decls;
                     ts_perm_decls = perm_decls;
                     ts_rvar_decls = rvar_decls;
                     ts_cipher = cipher };
                  tps_history = [] }
     in
     add_tproofState tps >>= fun proofId ->
     Lwt.return (Ok (`Int proofId)))
    (fun exn -> match exn with
       | CpaWrapError(field,s) ->
           Lwt.return (Error (`Assoc [("field", `String field); ("message", `String s) ]))
       | _ -> raise exn)

let handle_get_proof arg =
  let l = getAssoc arg in
  let proofId = getInt "proofId" l in
  get_tproofState proofId >>= fun mtps ->
  match mtps with
  | Some tps ->
      Lwt.return (Ok (proofstate_to_json tps))
  | None ->
      Lwt.return (InternalError "no_proof")

let handle_apply_proof arg =
  Lwt.catch 
    (fun () ->
     let l = getAssoc arg in
     let cmd = getString "cmd" l in
     let proofId = getInt "proofId" l in
     get_tproofState proofId >>= fun mtps ->
     match mtps with
     | Some tps ->
         Lwt.wrap (fun () -> apply cmd (ps_of_tps tps)) >>= fun ps' ->
         add_tproofState { tps with tps_history = ps'.ps_history } >>= fun proofId ->
         Lwt.return (Ok (`Int proofId))
     | None ->
         Lwt.return (InternalError "no_proof"))
    (fun exn -> match exn with
       | CpaWrapError(_,s) ->
           Lwt.return (Error (`Assoc [("field", `String "cmd"); ("message", `String s) ]))
       | _ -> raise exn)

(*
let handle_norm_expr arg =
  Lwt.catch 
    (fun () ->
     let l = getAssoc arg in
     let sexpr = getString "nexpr" l in
     let proofId = getInt "proofId" l in
     get_proofState proofId >>= fun mps ->
     match mps with
     | Some ps ->
         Lwt.wrap (fun () -> norm_for_path [] ps sexpr) >>= fun e' -> (* FIXME: add right path [10min] *)
         Lwt.return (Ok (`String (fsprintf "%a" E.pp_exp (rename_e e') |> fsget)))
     | None ->
         Lwt.return (InternalError "no_proof"))
    (fun exn -> match exn with
       | CpaWrapError(_,s) ->
           Lwt.return (Error (`Assoc [("field", `String "nexpr"); ("message", `String s) ]))
       | _ -> raise exn)

let handle_apply_ctxt arg =
  Lwt.catch 
    (fun () ->
     let l = getAssoc arg in
     let known   = getString "known" l in
     let context = getString "context" l in
     let proofId = getInt "proofId" l in
     get_proofState proofId >>= fun mps ->
     match mps with
     | Some ps ->
         Lwt.wrap (fun () -> apply_ctxt_for_path [] ps known context) >>= fun e' -> (* FIXME: add right path [10min] *)
         Lwt.return (Ok (`String (fsprintf "%a" E.pp_exp (rename_e e') |> fsget)))
     | None ->
         Lwt.return (InternalError "no_proof"))
    (fun exn -> match exn with
       | CpaWrapError(_,s) ->
           Lwt.return (Error (`Assoc [("field", `String "deduc"); ("message", `String s) ]))
       | _ -> raise exn)
*)

let handle_request cmd =
  Lwt.catch
    (fun () ->
     let m =
       match parse_req cmd with
       | Some ("start", arg)       -> handle_start arg
       | Some ("get_proof", arg)   -> handle_get_proof arg
       | Some ("apply_proof", arg) -> handle_apply_proof arg
       (* | Some ("norm_expr", arg)   -> handle_norm_expr arg *)
       (* | Some ("apply_ctxt", arg)  -> handle_apply_ctxt arg *)
       | _ -> Lwt.return (InternalError "handle_request: invalid command")
     in
     m >>= fun rep ->
     Lwt.return (YS.to_string (reply_to_json rep), "application/json"))
    (fun exn -> match exn with
       | CpaWrapError(_,s) ->
           Lwt.return (YS.to_string (reply_to_json (InternalError s)), "application/json")
       | JsonExtract s ->
           let err = P.sprintf "handle_request failed: %s" s in
           Lwt.return (YS.to_string (reply_to_json (InternalError err)), "application/json")
       | _ ->
           let err = P.sprintf "handle_request failed: %s" (Printexc.to_string exn) in
           Lwt.return (YS.to_string (reply_to_json (InternalError err)), "application/json"))

(* This is just a dummy GET *)
let proof_get_service =
  Eliom_registration.String.register_service
    ~path:["request"]
    ~get_params:Eliom_parameter.unit
      (fun () () -> Lwt.return ("GET not allowed", "text/plain"))


(* We use post requests to this URL for everything *)
let proof_post_service =
  let open Eliom_parameter in
  let () = () in (* FIXME *)
  Eliom_registration.String.register_post_service
    ~fallback:proof_get_service
    (* use check_only to disable modifying the proof, this can be used for checking before submitting *)
    ~post_params:(string "cmd")
      (fun () cmd -> handle_request cmd)
