open Util
open Type
open Expr 
open Game 
open TheoryState 

module Ht = Hashtbl

type pvar = string list * string

type mem  = string

type cnst = string


type op = 
 | Oopp (* prefix - *)
 | Opow (* ^ *)
 | Osub (* - *)
 | Oadd (* + *)
 | Omul (* * *)
 | Odiv (* / *)
 | Oeq
 | Ole
 | Ostr of string
 | Oand
 | Onot


type expr = 
  | Epv    of pvar 
  | Etuple of expr list
  | Eproj  of int * expr
  | Ecnst  of cnst
  | Eapp   of op * expr list
  | Eif    of expr * expr * expr 

type lvalue = pvar list

type mod_name = { mn : string;
                  ma : mod_name list }

let mod_name mn ma = { mn = mn; ma = ma }

type fun_name = mod_name * string
  
type instr = 
 | Iasgn of lvalue * expr
 | Irnd  of lvalue * ty * expr list
 | Icall of lvalue * fun_name * expr 
 | Iif   of expr * instr list * instr list

type fundef = {
  f_name  : string;
  f_param : (pvar * ty) list;
  f_local : (pvar * ty) list;
  f_res   : (pvar * ty) option;
  f_body  : instr list
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
  | Fapp of op * form list
  | Fif of form * form * form 
  | Fabs of form
  | Frofi of form (* int -> real *)
(*  | Fexists of (lvar * hvar) list * form *)
  | Fforall_mem of mem * form  
  | Fpr of fun_name * mem * form list * form

let f_true = Fcnst "true"
let f_not f = Fapp(Onot, [f])
let f_eq f1 f2 = Fapp(Oeq,[f1;f2])
let f_neq f1 f2 = f_not (f_eq f1 f2)
let f_le f1 f2 = Fapp(Ole,[f1;f2])
let f_and f1 f2 = Fapp(Oand, [f1; f2])
let f_rsub f1 f2 = Fapp(Osub, [f1;f2])
let f_radd f1 f2 = Fapp(Oadd, [f1;f2])
let f_rinv f = Fapp(Odiv, [Fcnst "1%r";f])
let f_2 = Fcnst "2"
let f_2pow f = Fapp(Opow, [f_2;f])
let f_Fq = Fcnst "F.q"

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


(* type ro_info = {
  h_th   : string;
  h_mod  : string;
  h_log  : string;
  h_fadv : string;
}
*)
  
type op_info = 
  { o_name : string }

type hash_kind = 
  | Hop of op_info 

type hash_info = {
  h_kind : hash_kind;
  h_eget : expr -> expr;
  h_fget : mem option -> form -> form;
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

type bmap_info = string

type file = {
  mutable top_name : Sstring.t;
  levar : tvar_info Lenvar.H.t;
  grvar : tvar_info Groupvar.H.t;
  hvar  : hash_info Hsym.H.t;
  bvar  : bmap_info Esym.H.t;
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
  bvar     = Esym.H.create 7;
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
 
let add_bilinear file bv = 
  let name = top_name file ("B" ^ Esym.name bv) in
  Esym.H.add file.bvar bv name
 
let add_bilinears file ts = 
  Ht.iter (fun _ bv -> add_bilinear file bv) ts.ts_emdecls
 
let bvar_mod file bv =
  try Esym.H.find file.bvar bv with Not_found -> assert false

let add_hash file h = 
  if Hsym.is_ro h then 
    assert false (* FIXME *)
  else
    let name = top_name file (Hsym.tostring h) in
    let info = { 
      h_kind = Hop {o_name = name };
      h_eget = (fun e -> Eapp(Ostr name, [e]));
      h_fget = (fun _ f -> Fapp(Ostr name, [f]));
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

let bs_length file lv = 
  Fcnst(lvar_mod file lv ^ ".length")

