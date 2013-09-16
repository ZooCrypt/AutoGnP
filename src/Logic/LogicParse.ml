open Logic
open Type
open Expr

module PU = ParserUtil
module P  = Printf

type tyMap = ty Mstring.t

type sym =
    SRsym of Rsym.t
  | SPsym of Psym.t
  | SHsym of Hsym.t

type symMap = sym Mstring.t

type tenv = {
  mutable te_ty_m    : tyMap;
  mutable te_sym_m   : symMap;
  mutable te_msg_ty  : ty option;
}

let empty_tenv = {
    te_ty_m   = Mstring.empty;
    te_sym_m  = Mstring.empty;
    te_msg_ty = None;
  }

exception TenvUndef of string * string

(* ****************************************************************** *)
(* Lookup symbols in tenv *)

let getTyVar te s =
  try Mstring.find s te.te_ty_m
  with Not_found ->
    let ty = mk_ty [ Tyvar.mk s ] in
    te.te_ty_m <- Mstring.add s ty te.te_ty_m;
    ty

let getTy te (ss : PU.ity) : ty =
  ty_concat_l (List.map (getTyVar te) ss)

let getRsym te s =
  try
    match Mstring.find s te.te_sym_m with
    | SRsym rsym -> rsym
    | _ -> failwith (Printf.sprintf "getRsym: ``%s'' not a random variable symbol" s)
  with
    Not_found -> raise (TenvUndef("random variable", s))

let getHsym te s =
  try
    match Mstring.find s te.te_sym_m with
    | SHsym hsym -> hsym
    | _ -> failwith (Printf.sprintf "getHsym: ``%s'' not a hash symbol" s)
  with
    Not_found -> raise (TenvUndef("hash function", s))

let getPsym te s =
  try
    match Mstring.find s te.te_sym_m with
    | SPsym psym -> psym
    | _ -> failwith (Printf.sprintf "getPsym: ``%s'' not a permutation symbol" s)
  with
    Not_found -> raise (TenvUndef("permutation", s))

(* ****************************************************************** *)
(* Add and convert symbols *)

let addSym te s sym =
  te.te_sym_m <- Mstring.add s sym te.te_sym_m

let addTyVar te ty =
  match ty.ty_sum with
  | [tyv] -> te.te_ty_m <- Mstring.add (Tyvar.name tyv) ty te.te_ty_m;
  | _     -> ()
  (* FIXME: add some check to prevent overwriting with different value *)


let convert_hsyms te hdecls =
  let go (name, dom, codom) =
    addSym te name (SHsym (Hsym.mk name (getTy te dom) (getTy te codom)))
  in
  List.iter go hdecls

let convert_psyms te pdecls =
  let go (name, dom) =
    addSym te name (SPsym (Psym.mk name (getTy te dom)))
  in
  List.iter go pdecls

let convert_rsyms te rdecls =
  let go (name, ity) =
    addSym te name (SRsym (Rsym.mk name (getTy te ity)))
  in
  List.iter go rdecls

let te_of_cj cj =
  let te = empty_tenv in
  let rec addAskHsyms ev = match ev with
    | Guess | Eq _ -> ()
    | Ask(hs, _)   ->
        addTyVar te hs.Hsym.dom; addTyVar te hs.Hsym.codom;
        addSym te (Id.name hs.Hsym.id) (SHsym hs)
    | Conj evs     -> List.iter addAskHsyms evs
  in
  let go e =
    addTyVar te e.e_ty;
    match e.e_node with
    | V Msg -> te.te_msg_ty <- Some e.e_ty
    | R rs  -> addSym te (Id.name rs.Rsym.id) (SRsym rs)
    | Pinv(ps,_) | P(ps,_) ->
        addSym te (Id.name ps.Psym.id) (SPsym ps)
    | H(hs,_) ->
        addSym te (Id.name hs.Hsym.id) (SHsym hs)
    | _ -> ()
  in
  addAskHsyms cj.cj_ev;
  iter_expr_cj (e_iter go) cj;
  te

(* ****************************************************************** *)
(* Convert expression *)

let isPsym te s =
  try  match Mstring.find s te.te_sym_m with
       | SPsym _ -> true
       | _       -> false
  with Not_found -> false

let rec convert_expr ?star te e =
  let go = convert_expr ?star te in
  match e with
  | PU.IZ(ity)            -> mk_Z (getTy te ity)
  | PU.IMsg               -> (match te.te_msg_ty, star with
                              | Some ty, None -> mk_Msg ty (* contexts cannot contain Msg *)
                              | _ -> failwith "convert_expr: message type undefined")
  | PU.IStar              -> (match star with
                              | Some ty -> mk_Star ty
                              | None    -> failwith "convert_expr: type for Star undefined")
  | PU.IR(s)              -> mk_R (getRsym te s)
  | PU.IFun(s,e)          -> if isPsym te s
                             then mk_P (getPsym te s) (go e)
                             else mk_H (getHsym te s) (go e)
  | PU.IPinv(s,e)         -> mk_P (getPsym te s) (go e)
  | PU.IApp(es)           -> mk_App (List.map go es)
  | PU.IProj((it1,it2),e) -> mk_Proj2 (getTy te it1, getTy te it2) (go e)
  | PU.IXor(e1, e2)       -> mk_Xor (go e1) (go e2)

(* ****************************************************************** *)
(* Declare schemes *)

exception CpaWrapError of (string * string)

let wrapError f =
  let cfield = ref "" in
  try
    f cfield
  with
    | TenvUndef(t,name) -> raise (CpaWrapError(!cfield, P.sprintf "%s ``%s'' undefined" t name))
    | Parse.ParseError s -> raise (CpaWrapError(!cfield, s))
    | Expr.TypeError(ty1 ,ty2, me1, me2, s) ->
         let s = typeError_to_string_rn (ty1,ty2,me1,me2,s) in
         raise (CpaWrapError(!cfield, s))
    | InvalidPath(_,p,s) ->
        raise (CpaWrapError("cmd", Printf.sprintf "%s: invalid path  %s" s
                 (List.fold_left (fun s i -> if s <> "" 
                                  then Printf.sprintf "%i, %s" i s
                                  else string_of_int i) "" (List.rev p))))
    | AppFailure(_,s) -> raise (CpaWrapError("cmd",s))

let declare_scheme msg_decl hash_decls perm_decls rvar_decls cipher =
  wrapError (fun cfield -> 
    let ty_m = Mstring.empty in
    let sym_m = Mstring.empty in
    let te = { te_ty_m = ty_m; te_sym_m = sym_m;
               te_msg_ty = None }
    in
    cfield := "msg_decl";
    let msg_ty = getTy te (Parse.ty msg_decl) in
    te.te_msg_ty <- Some msg_ty; 
    cfield := "rvar_decls";
    convert_rsyms te (Parse.const_decls rvar_decls);
    cfield := "hash_decls";
    convert_hsyms te (Parse.op_decls hash_decls);
    cfield := "perm_decls";
    convert_psyms te (Parse.const_decls perm_decls);
    cfield := "cipher";
    let cipher = convert_expr te (Parse.expr cipher) in
    mk_cp CpaAdmit { cj_cipher = cipher; cj_ev = Guess } [])

