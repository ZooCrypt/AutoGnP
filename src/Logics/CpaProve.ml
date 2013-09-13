open Type
open Cpa
open Expr
open Id

module PU = ParserUtil
module P = Printf
module L = List
module CP = CpaParse

(* ----------------------------------------------------------------------- *)
(** {1 Proofstate: proof + typing environment} *)

(* move back later on *)
type proofState = {
  ps_history : string list;
  ps_proof   : cpaProof
}

(* ----------------------------------------------------------------------- *)
(** {2 Initial proof generation and rule application} *)

(* FIXME: refactor apply to return sequence of (located) rule labels. *)
let apply cmd ps0 =
  CP.wrapError (fun _ ->
    (* I will get rid of history hack *)
    let cmd' = if (String.get cmd ((String.length cmd) - 1) = ';') then cmd else cmd ^ ";" in
    let ps = { ps0 with  ps_history = ps0.ps_history @ [cmd'] } in

    let ensure_fresh rn ju =
      if Se.exists (fun e -> name (destr_R e).Rsym.id = rn) (rvars_cj ju) then
        raise (CP.CpaWrapError("cmd", Printf.sprintf "random variable %s not fresh" rn))
    in
    let handleCmd c ps =
      let prf = ps.ps_proof in
      let path = match snd c with
        | PU.LPath p -> p
        | PU.LAdmit i ->
            let adms = admitPaths prf in
            if i < List.length adms then List.nth adms i
            else raise (InvalidAdmit(prf,i,"apply"))
      in
      let ju = cjAt path prf in
      let te = CP.te_of_cj ju in
      let app tac prf = applyAt path tac prf in

      match fst c with
      | PU.CAdmit -> 
          { ps with ps_proof = app appAdmit prf }
      | PU.CNorm ->
          { ps with ps_proof = app appNorm prf }
      | PU.CConj(i) ->
          { ps with ps_proof = app (appConj i) prf }
      | PU.COpt(rn,ie) ->
          let r = CP.getRsym te rn in
          let e = CP.convert_expr te ie in
          if (Se.mem (mk_R r) (e_rvars e)) 
          then raise (CP.CpaWrapError("cmd", "opt (r) (e): random variable r occurs in expression e"));
          { ps with ps_proof = app (appOpt r e) prf }
      | PU.CPerm(rn,fn) ->
          let r = CP.getRsym te rn in
          let f = CP.getPsym te fn in
          { ps with ps_proof = app (appPerm r f) prf }
      | PU.CSplit(r,it1,r1n,r2n) ->
          (let r = CP.getRsym te r in 
           let ty1 = CP.getTy te it1 in
           ensure_fresh r1n ju;
           let r1 = Rsym.mk r1n ty1 in
           match ty_minus r.Rsym.ty ty1 with
           | Some ty2 when not (is_ty_zero ty2 || is_ty_zero ty1) -> 
               ensure_fresh r2n ju;
               let r2 = Rsym.mk r2n ty2 in
               { ps with ps_proof = app (appSplit r r1 r2) prf }
           | _ -> raise (CP.CpaWrapError("cmd", Printf.sprintf "invalid type for %s" r1n)))
      | PU.CMerge(r1n,r2n,rn) ->
          let r1 = CP.getRsym te r1n in
          let r2 = CP.getRsym te r2n in
          let tyr = ty_concat r1.Rsym.ty r2.Rsym.ty in
          ensure_fresh rn ju;
          let r = Rsym.mk rn tyr in
          { ps with ps_proof = app (appMerge r1 r2 r) prf }
      | PU.CFail1(hn,rn) ->
          let h = CP.getHsym te hn in
          let tyr = h.Hsym.codom in
          ensure_fresh rn ju;
          let r = Rsym.mk rn tyr in
          { ps with ps_proof = app (appFail1 h r) prf }
      | PU.CFail2(hn,rn) ->
          let h = CP.getHsym te hn in
          let tyr = h.Hsym.codom in
          ensure_fresh rn ju;
          let r = Rsym.mk rn tyr in
          { ps with ps_proof = app (appFail2 h r) prf }
      | PU.CInd ->
          {ps with ps_proof = app appInd prf }
      | PU.CRnd(rn, ic) ->
          let r = CP.getRsym te rn in
          let qes = askEventMessages ju.cj_ev in
          let ty = ty_concat_l (List.map (fun x -> x.e_ty) qes) in
          let c = CP.convert_expr ~star:ty te ic in
          { ps with ps_proof = app (appRnd r c) prf }
      | PU.COw(fn,r1n,t1n,t2n,r2ns,ic1,ic2) ->
          let r2vs = List.map (CP.getRsym te) r2ns in
          let r1v = CP.getRsym te r1n in
          let qes = askEventMessages ju.cj_ev in
          let qes_ty = ty_concat_l (List.map (fun x -> x.e_ty) qes) in
          let r2s_ty = ty_concat_l (List.map (fun x -> x.Rsym.ty) r2vs) in
          let msg_ty = match find_msg ju with
            | Some m -> m.e_ty
            | None   -> ty_concat_l []
          in
          let star1_ty = ty_concat_l [qes_ty; r2s_ty; msg_ty] in
          let c1 = CP.convert_expr ~star:star1_ty te ic1 in
          let star2_ty = ty_concat_l [r1v.Rsym.ty; r2s_ty; msg_ty] in
          let c2 = CP.convert_expr ~star:star2_ty te ic2 in
          let t1 = CP.getTy te t1n in
          let t2 = CP.getTy te t2n in
          let f  = CP.getPsym te fn in
          { ps with ps_proof = app (appOw f r1v t1 t2 r2vs c1 c2) prf }
    in    
    let rec go cs ps = match cs with
      | [] -> ps
      | c::cs -> go cs (handleCmd c ps)
    in go (Parse.cmds cmd) ps)

(*
let norm_for_path path ps se =
  CP.wrapError (fun _ ->
    let ju = failwith "FIXME: not implemented yet" in (* maybe 10 min *)
    let ie = Parse.expr se in
    let e = CP.convert_expr ju ie in
    Norm.norm e)

let apply_ctxt_for_path path ps sknown sctxt =
  CP.wrapError (fun _ ->
    let ju = failwith "FIXME: not implemented yet" in (* maybe 10 min *)
    let iknown = Parse.expr sknown in
    let known = CP.convert_expr ju iknown in
    let ictxt = Parse.expr sctxt in
    let ctxt = CP.convert_expr ~star:known.e_ty ju ictxt in
    Norm.norm (e_replace (mk_V Star known.e_ty) known ctxt))
*)

(* ----------------------------------------------------------------------- *)
(** {4 Textual Proofstate: types, cipher + history} *)

(* FIXME: save parsed representations where possible, e.g., use ity, iexpr.
          note that these do not exist yet for all commands *) 

type tscheme = {
  ts_msg_decl   : string;
  ts_hash_decls : string;
  ts_perm_decls : string;
  ts_rvar_decls : string;
  ts_cipher     : string
}

type tproofState = {
  tps_scheme  : tscheme;
  tps_history : string list;
}

let ps_of_tps tps : proofState =
  let ts = tps.tps_scheme in
  let cp = CP.declare_scheme ts.ts_msg_decl ts.ts_hash_decls ts.ts_perm_decls ts.ts_rvar_decls ts.ts_cipher in
  let ps0 = { ps_history = []; ps_proof = cp } in
  L.fold_left (fun ps cmd -> apply cmd ps) ps0 tps.tps_history