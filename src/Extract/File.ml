open Abbrevs
open Util
open Type
open Game
open Syms
open Gsyms
open TheoryTypes

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
 | Oiff 
 | Oimp
 | Ole
 | Olt
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

let e_pv pv = Epv pv
let e_eq e1 e2 = Eapp(Oeq,[e1;e2])
let e_add e1 e2 = Eapp(Oadd, [e1;e2])
let e_sub e1 e2 = Eapp(Osub, [e1;e2])
let e_int n = Ecnst (string_of_int n)
let e_int0 = e_int 0
let e_int1 = e_int 1
let e_incr e = e_add e e_int1
let e_lt e1 e2 = Eapp(Olt, [e1;e2])

type lvalue = pvar list

type mod_name = { mn : string;
                  ma : mod_name list }

let mod_name mn ma = { mn = mn; ma = ma }

type fun_name = mod_name * string
  
type instr = 
 | Iasgn of lvalue * expr
 | Irnd  of lvalue * ty * expr list
 | Irnd_int of lvalue * expr * expr
 | Icall of lvalue * fun_name * expr list
 | Iif   of expr * instr list * instr list

type fun_def = {
  f_param : (pvar * ty) list;
  f_local : (pvar * ty) list;
  f_res   : (pvar * ty) option;
  f_body  : instr list
} 

type fun_def1 = 
 | Fbody of fun_def
 | Falias of fun_name
  
type fundef = {
  f_name  : string;
  f_def   : fun_def1
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

let subst_mod ms = 
  let get s = try Mstring.find s ms with Not_found -> {mn = s; ma = []} in
  let rec aux md = 
    let md' = get md.mn in
    { md' with ma = md'.ma @ List.map aux md.ma } in
  aux

let subst_f ms mc f = 
  let subst_mod = subst_mod ms in
  let rec aux f = 
    match f with
    | Fpr ((md,f),m,a,ev) -> Fpr((subst_mod md, f), m, a, ev) 
    | Fapp(op, fs)        -> Fapp(op, List.map aux fs)
    | Fabs f              -> Fabs (aux f)
    | Frofi f             -> Frofi (aux f)
    | Fcnst s             -> (try Mstring.find s mc with Not_found -> f)
    | Fforall_mem(m,f)    -> Fforall_mem(m, aux f)
    | _                   -> f in
  aux f

type mod_ty = {
  modt_name : string;
  modt_param : (string * string) list;
  modt_proc  : (string * (string option * ty) list * ty * fun_name list) list
} 

type orcl_info = { 
  mutable obound  : string;
  oparams : Vsym.t list;
  ores    : ty;
(*  obody   : lcmd list;
  ores    : Expr.expr; *)
} 
  
type game_info = {
  oinfo : orcl_info Osym.H.t;
  ainfo : (Osym.t list) Asym.H.t;
} 


type adv_info = {
  adv_name  : string;
  adv_ty    : string;
  adv_oty   : string;
  mutable adv_restr : string list;
  adv_g    : game_info 
}


type proof = F.formatter -> unit -> unit

type clone_with = 
  | CWtype of string * ty 
  | CWop   of string * (pvar * ty * pvar list) option * expr

type clone_info =
  { 
    ci_local  : bool;
    ci_import : bool;
    ci_from   : string;
    ci_as     : string;
    ci_with   : clone_with list;
    ci_proof  : (string * proof) list;
  }
      
    
type cmd =
  | Ccomment of string 
  | Cbound of string
  | Cmodty of mod_ty
  | Cmod   of bool * mod_def
  | Cclone of clone_info
  | Clemma of bool * string * form * proof option
  | Csection of section

and section =
  {         section_name : string;
    mutable game_trans   : (gdef * mod_def) list;
    mutable tosubst      : string list;
    mutable section_top  : cmd list;            
    mutable section_glob : cmd list;
    mutable section_loc  : local_section option;
  }
    
and local_section = {
          adv_info     : adv_info;
  mutable loca_decl    : cmd list 
}

(* type ro_info = {
  h_th   : string;
  h_mod  : string;
  h_log  : string;
  h_fadv : string;
}
*)


let f_v g pv m = Fv (([g.mod_name],snd pv),Some m)

let f_true = Fcnst "true"
let f_not f = Fapp(Onot, [f])
let f_iff f1 f2 = Fapp(Oiff, [f1;f2])
let f_imp f1 f2 = Fapp(Oimp, [f1;f2])
let f_eq f1 f2 = Fapp(Oeq,[f1;f2])
let f_neq f1 f2 = f_not (f_eq f1 f2)
let f_le f1 f2 = Fapp(Ole,[f1;f2])
let f_and f1 f2 = Fapp(Oand, [f1; f2])
let f_rsub f1 f2 = Fapp(Osub, [f1;f2])
let f_radd f1 f2 = Fapp(Oadd, [f1;f2])
let f_rmul f1 f2 = Fapp(Omul, [f1;f2])
let f_rinv f = Fapp(Odiv, [Fcnst "1%r";f])
let f_2 = Fcnst "2"
let f_2pow f = Fapp(Opow, [f_2;f])
let f_Fq = Fcnst "F.q"
let f_r0 = Frofi (Fcnst "0")

let get_pr_ev = function
  | Fpr(_,_,_,ev) -> ev
  | _ -> assert false

type tvar_info = {
  tvar_mod : string;
  tvar_ty  : string;
}
  
type op_info = 
  { o_name : string }

type hash_kind = 
  | Hop of op_info 

type hash_info = {
  h_kind : hash_kind;
  h_eget : expr -> expr;
  h_fget : mem option -> form -> form;
}         
                         
type assumption_dec_info = {
  ad_name  : string;
  ad_priv  : Vsym.S.t; 
  ad_param : Vsym.t list;
  ad_advty : string;
  ad_cmd1  : mod_def;
  ad_len1  : int;
  ad_cmd2  : mod_def;
  ad_len2  : int;
}

type assumption_comp_info = {
  ac_name  : string;
  ac_priv  : Vsym.S.t;
  ac_param : Vsym.t list;
  ac_advret: ty;
  ac_advty : string;
  ac_cmd   : mod_def;
  ac_len   : int;
}

type bmap_info = string

(*type open_section = {
          osection_name : string;
  mutable game_trans   : (gdef * mod_def) list;
  mutable osection_top     : cmd list;
  mutable osection_glob : cmd list;
  mutable osection_loc  : local_section option;
}*)
  
type file = {
  mutable top_name : Sstring.t;
  levar : tvar_info Lenvar.H.t;
  grvar : tvar_info Groupvar.H.t;
  hvar  : hash_info Hsym.H.t;
  bvar  : bmap_info Esym.H.t;
  assump_dec  : (string, assumption_dec_info) Ht.t;
  assump_comp : (string, assumption_comp_info) Ht.t;
  mutable top_decl    : cmd list;
  mutable open_section    : section list;
}


let add_top_name file s = 
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
  add_top_name file s;
  s

let empty_file = 
  let empty = {
    top_name     = Sstring.empty;
    levar        = Lenvar.H.create 7;
    grvar        = Groupvar.H.create 7;
    hvar         = Hsym.H.create 7;
    bvar         = Esym.H.create 7;
    assump_dec   = Ht.create 3;
    assump_comp  = Ht.create 3;
    top_decl     = [];
    open_section = [];
  } in
  ignore (add_top_name empty "OrclTest");
  empty

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
    failwith "No able to extract random oracle for the moment"
  else
    let name = top_name file (Hsym.to_string h) in
    let info = { 
      h_kind = Hop {o_name = name };
      h_eget = (fun e -> Eapp(Ostr name, [e]));
      h_fget = (fun _ f -> Fapp(Ostr name, [f]));
    } in
    Hsym.H.add file.hvar h info
 
let add_hashs file ts = 
  Ht.iter (fun _ h -> add_hash file h) ts.ts_rodecls

let gvar_mod file gv = 
  (Groupvar.H.find file.grvar gv).tvar_mod

let lvar_mod file lv = 
  (Lenvar.H.find file.levar lv).tvar_mod

let bs_length file lv = 
  Fcnst(lvar_mod file lv ^ ".length")

let get_section file = 
  match file.open_section with
  | [] -> assert false
  | s::_ -> s

let get_lsection file = 
  let s = get_section file in
  match s.section_loc with
  | None -> assert false
  | Some sl -> sl

let add_top file c = 
  let s = get_section file in
  s.section_top <- c :: s.section_top;
  match c with
  | Cmod(_,mod_def) -> s.tosubst <- mod_def.mod_name :: s.tosubst
  | _ -> ()

let add_glob file c = 
  let s = get_section file in
  s.section_glob <- c :: s.section_glob

let add_local file c = 
  let s = get_lsection file in
  s.loca_decl <- c :: s.loca_decl

let add_def file local c =
  match local with
  | `Top    -> add_top file c
  | `Global -> add_glob file c
  | `Local  -> add_local file c

let start_section file name = 
  let sec_name = top_name file name in
  let sec = {
    section_name = sec_name;
    game_trans   = [];
    tosubst      = [];
    section_top  = [];
    section_glob = [];
    section_loc  = None;
  } in
  file.open_section <- sec :: file.open_section;
  sec_name

let end_section file = 
  match file.open_section with
  | [] -> assert false
  | s::ss ->
    file.top_decl <- 
      Csection s :: 
         Ccomment (Format.sprintf "{ section %s }" s.section_name) ::
         file.top_decl;
    file.open_section <- ss

(* Adv info *)
let adv_info file = (get_lsection file).adv_info

let adv_decl file =
  let i = adv_info file in
  i.adv_name, i.adv_ty

let adv_name file = 
  let i =  adv_info file in
  i.adv_name
  
let adv_mod file = {mn = adv_name file; ma = []}


(* Initialize the adversary info *)
let oname o = "o" ^ Osym.to_string o 
let omod = { mn = "O"; ma = [] }
let oOname o = omod, oname o 

let game_info file gdef = 
  let otbl = Osym.H.create 7 in
  let atbl = Asym.H.create 3 in
  let add_oinfo (o, params, _body, e) = 
    assert (not (Osym.H.mem otbl o));
    let qname = top_name file ("q" ^ oname o) in
    add_top file (Cbound qname);
    add_top file (Clemma (false, qname^"_pos", 
                          f_le f_r0 (Frofi (Fcnst qname)), None));
    let info = { 
      obound  = qname; 
      oparams = params; 
      ores    = e.Expr.e_ty } in
    Osym.H.add otbl o info in
  let make_info i =
    match i with
    | GCall(_,a,_,odef) ->
      List.iter add_oinfo odef;    
      Asym.H.add atbl a (List.map (fun (o,_,_,_) -> o) odef)
    | _ -> () in
  List.iter make_info gdef;
  { oinfo = otbl; ainfo = atbl } 

let init_adv_info file gdef = 
  assert ((get_section file).section_loc = None);
  let ginfo = game_info file gdef in

  let oty_name = top_name file "Orcl" in
  let aty_name = top_name file "Adv" in
  let a_name   = top_name file "A" in

  (* add the module type Orcl *)

  let oty = {
    modt_name  = oty_name;
    modt_param = [];
    modt_proc  = 
      Osym.H.fold (fun o od l ->
        let oname  = oname o in
        let params = 
          List.map (fun v -> Some (Vsym.to_string v), v.Vsym.ty) od.oparams in
        let rty    = od.ores in
        ( oname, params, rty, [])::l) ginfo.oinfo [];
  } in
  add_top file (Cmodty oty);
  
  (* add the module type of Adv *)
  
  let aty = {
    modt_name = aty_name;
    modt_param = ["O", oty_name];
    modt_proc = 
      Asym.H.fold (fun a os l ->
        let aname  = "a" ^ Asym.to_string a in
        let params = [ None, a.Asym.dom ] in
        let rty    = a.Asym.codom in
        (aname, params, rty, List.map oOname os)::l) ginfo.ainfo [];
  } in
  add_top file (Cmodty aty);
  let adv_info =
    { adv_name  = a_name;
      adv_ty    = aty_name;
      adv_oty   = oty_name;
      adv_restr = [];
      adv_g = ginfo } in
  let section_loc = {
    adv_info;
    loca_decl = []
  } in
  let s = get_section file in
  s.section_loc <- Some section_loc


let find_game file g = 
  let s = get_section file in
  snd (List.find (fun (g',_m) -> gdef_equal g g') s.game_trans)

let add_restr file modu =
  let ai = adv_info file in
  ai.adv_restr <- modu.mod_name :: ai.adv_restr
  
let add_game file local modu = 
  let loc = local = `Local in
  add_def file local (Cmod (loc,modu));
  if not loc then add_restr file modu
  
let bind_game file local g modu = 
  add_game file local modu;
  let s = get_section file in
  s.game_trans <- (g,modu) :: s.game_trans

let is_MCvar = function
  | MCvar _ -> true
  | _ -> false

let f_body f = 
  match f.f_def with
  | Fbody fd -> fd.f_body
  | _ -> assert false
