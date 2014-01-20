open Util
open Type
open Expr 
open Game 
open TheoryState 

module Ht = Hashtbl

type pvar = string list * string

type mem  = string

type cnst = string

type expr = 
  | Epv    of pvar 
  | Etuple of expr list
  | Eproj  of int * expr
  | Ecnst  of cnst
  | Eapp   of string * expr list
  | Eif    of expr * expr * expr 
  | Eeq    of expr * expr

type lvalue = pvar list

type mod_name = { mn : string;
                  ma : mod_name list }

let mod_name mn ma = { mn = mn; ma = ma }

type fun_name = mod_name * string
  
type instr = 
 | Iasgn of lvalue * expr
 | Irnd  of lvalue * ty
 | Icall of lvalue * fun_name * expr 
 | Iif   of expr * instr list * instr list

type fundef = {
  f_name : string;
  f_param : (pvar * ty) list;
  f_local : (pvar * ty) list;
  f_res   : (pvar * ty) option;
  f_body : instr list
}

type mod_body = 
  | Mod_def of mod_comp list
  | Mod_alias of mod_name

and mod_comp = 
  | MCmod of mod_def
  | MCfun of fundef 
  | MCvar of pvar * ty
  
and mod_def = {
  mod_name : string;
  mod_param : (string * string) list;
  mod_body : mod_body
}  

type form = 
  | Fv of pvar * mem option
  | Ftuple of form list
  | Fproj of int * form
  | Fcnst of cnst
  | Fapp of string * form list
  | Fif of form * form * form 
  | Feq of form * form
  | Fle of form * form
  | Fabs of form
(*  | Fexists of (lvar * hvar) list * form *)
  | Fforall_mem of mem * form  
  | Fpr of fun_name * mem * form list * form

let f_true = Fapp("true",[])
let f_and f1 f2 = Fapp("(/\\)", [f1; f2])
let f_rsub f1 f2 = Fapp("Real.(-)", [f1;f2])
let f_radd f1 f2 = Fapp("Real.(+)", [f1;f2])

let get_pr_ev = function
  | Fpr(_,_,_,ev) -> ev
  | _ -> assert false

type proof = Format.formatter -> unit -> unit

type cmd = 
  | Cmod   of mod_def
  | Clemma of bool * string * form * proof option

type tvar_info = {
  tvar_mod : string;
  tvar_ty  : string;
}

(* 
   si pas rnd oracle
     (* Partage par tout le monde *)
     module type HashOrcl = {
       fun hash(_:t1) : t2 
     }.
     (* Specifique *)
     theory Hxxx.
       op h : t1 -> t2.
       module H = { 
         var log : t1 list
         fun hash(x:t1) : t2 = { 
            log = x::log;
            return h x;
         }
       }.
     end.
   si rnd oracle
   module H = {
     var m : (t1,t2) map
     var log : t1 list
     fun init () : unit = {
        blabla
     }
     fun hash (x:t1) : t2 = {
        log = x::log;
        return m.[x];
     }
   }
*)

type hash_info = {
  h_rnd  : bool;
  h_th   : string;
  h_mod  : string;
  h_eget : expr -> expr;
  h_fget : mem option -> form -> form;
  h_log  : string;
  h_fadv : string;
}         

type orcl_info = { 
  oparams : Vsym.t list;
  obody   : lcmd list;
  ores    : Expr.expr;
} 

type game_info = {
  oinfo : orcl_info Osym.H.t;
  ainfo : (Osym.t list) Asym.H.t;
}

let check_game_info i1 i2 = 
  assert (Osym.H.length i1.oinfo = Osym.H.length i2.oinfo);
  assert (Asym.H.length i1.ainfo = Asym.H.length i2.ainfo);
  Osym.H.iter (fun o oi1 ->
    assert (Osym.H.mem i2.oinfo o);
    let oi2 = Osym.H.find i2.oinfo o in
    assert
      (try List.for_all2 (fun v1 v2 -> ty_equal v1.Vsym.ty v2.Vsym.ty) 
             oi1.oparams oi2.oparams
       with Invalid_argument _ -> false);
    assert (ty_equal oi1.ores.e_ty oi2.ores.e_ty)) i1.oinfo;
  Asym.H.iter (fun a l1 ->
    let l2 = Asym.H.find i2.ainfo a in
    assert
      (try List.for_all2 (fun o1 o2 -> Osym.equal o1 o2) l1 l2
       with Invalid_argument _ -> false)) i1.ainfo
      
let game_info gdef = 
  let otbl = Osym.H.create 7 in
  let atbl = Asym.H.create 3 in
  let add_oinfo (oname, params, body, e) = 
    assert (not (Osym.H.mem otbl oname));
    let info = { oparams = params; obody = body; ores = e } in
    Osym.H.add otbl oname info in
  let make_info i =
    match i with
    | GCall(_,a,_,odef) ->
      List.iter add_oinfo odef;
      Asym.H.add atbl a (List.map (fun (o,_,_,_) -> o) odef)
    | _ -> () in
  List.iter make_info gdef;
  { oinfo = otbl; ainfo = atbl }
      
type adv_info = {
  adv_name : string;
  adv_ty   : string;
  adv_g    : game_info
}
                      
type assumption_info = {
  a_name  : string;
  a_priv  : Vsym.S.t; 
  a_param : Vsym.t list;
  a_advty : string;
  a_cmd1  : mod_def;
  a_len1  : int;
  a_cmd2  : mod_def;
  a_len2  : int;
}

type file = {
  mutable top_name : Sstring.t;
  levar : tvar_info Lenvar.H.t;
  grvar : tvar_info Groupvar.H.t;
  hvar  : hash_info Hsym.H.t;
  assump : (string, assumption_info) Ht.t;
  mutable game_trans : (gdef * mod_def) list;
  mutable glob_decl  : cmd list;
  mutable adv_info   : adv_info option;
  mutable loca_decl  : cmd list;
}

let empty_file = {
  top_name = Sstring.empty;
  levar    = Lenvar.H.create 7;
  grvar    = Groupvar.H.create 7;
  hvar     = Hsym.H.create 7;
  assump   = Ht.create 3;
  game_trans = [];
  glob_decl  = [];
  adv_info   = None;
  loca_decl  = []
}

let add_top file s = 
  assert (not (Sstring.mem s file.top_name));
  file.top_name <- Sstring.add s file.top_name

let top_name file s = 
  let s = 
    if Sstring.mem s file.top_name then
      let rec aux i = 
        let s = s ^ string_of_int i in
        if Sstring.mem s file.top_name then aux (i+1)
        else s in
      aux 0
    else s in
  add_top file s;
  s

let add_lvar file lv = 
  let name = top_name file ("BS_" ^ Lenvar.name lv) in
  let info = {
    tvar_mod = name;
    tvar_ty  = "word";
  } in
  Lenvar.H.add file.levar lv info
  
let add_lvars file ts = 
  Ht.iter (fun _ lv -> add_lvar file lv) ts.ts_lvars

let get_lvar file lv = 
  try Lenvar.H.find file.levar lv with Not_found -> assert false

let mod_lvar file lv = {mn = (get_lvar file lv).tvar_mod; ma = []}

let add_gvar file gv = 
 let name = top_name file ("G" ^ Groupvar.name gv) in
  let info = {
    tvar_mod = name;
    tvar_ty  = "group";
  } in
  Groupvar.H.add file.grvar gv info

let add_gvars file ts = 
  Ht.iter (fun _ gv -> add_gvar file gv) ts.ts_gvars

let get_gvar file gv = 
  try Groupvar.H.find file.grvar gv with Not_found -> assert false

let mod_gvar file gv = {mn = (get_gvar file gv).tvar_mod; ma = []}
 
let add_bilinears _file _ts = ()
 
let add_hash file h = 
  let name = top_name file (Hsym.tostring h) in
  let hname = name^".h" in
  let info = { 
    h_rnd  = false;
    h_th   = name;
    h_mod  = "H";
    h_eget = (fun e -> Eapp(hname, [e]));
    h_fget = (fun _ f -> Fapp(hname, [f]));
    h_log  = "log";
    h_fadv = "hash"
  } in
  Hsym.H.add file.hvar h info
 
let add_hashs file ts = 
  Ht.iter (fun _ h -> add_hash file h) ts.ts_rodecls



let add_adv local file ginfo =
  match file.adv_info with
  | None ->
    assert (local = false);
    let info = 
      { adv_name = top_name file "A";
        adv_ty   = top_name file "Adv";
        adv_g    = ginfo;
      } in
    file.adv_info <- Some info
  | Some info -> check_game_info info.adv_g ginfo
    

let adv_decl file = 
  match file.adv_info with
  | None -> assert false
  | Some i -> (i.adv_name,i.adv_ty)

let adv_name file = 
  match file.adv_info with
  | None -> assert false
  | Some i -> i.adv_name

let adv_info file = 
  match file.adv_info with
  | None -> assert false
  | Some i -> i
  
let adv_mod file = {mn = adv_name file; ma = []}

let gvar_mod file gv = 
  (Groupvar.H.find file.grvar gv).tvar_mod

let lvar_mod file lv = 
  (Lenvar.H.find file.levar lv).tvar_mod

