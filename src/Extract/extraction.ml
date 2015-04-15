open Abbrevs
open Util
open Type
open Expr
open ExprUtils
open Game 
open TheoryTypes
open TheoryState
open CoreTypes
open CoreRules
open File
open Syms
open Gsyms

module Ht = Hashtbl



(** game translation *)

let pvar modn v = 
  modn, Vsym.to_string v

let globals gdef = 
  let glob = gdef_global_vars gdef in
  List.map (fun e ->
     let v = destr_V e in 
     MCvar(pvar [] v, v.Vsym.ty)) (Se.elements glob) 

let mk_eget file h e = 
  let hi = Hsym.H.find file.hvar h in
  hi.h_eget e

let mk_fget file mem h f = 
  let hi = Hsym.H.find file.hvar h in
  hi.h_fget mem f

let string_of_op file = function
  | GExp gv -> (gvar_mod file gv) ^ ".(^)"
  | GLog gv -> (gvar_mod file gv) ^ ".log"
  | GInv    -> assert false
  | FOpp    -> "F.([-])"
  | FMinus  -> "F.(-)"
  | FInv    -> "F.inv"
  | FDiv    -> "F.(/)"
  | Eq      -> assert false
  | Not     -> assert false 
  | Ifte    -> assert false
  | EMap _  -> assert false

let op_of_op file = function
  | GExp _  -> Opow
  | GLog gv -> Ostr ((gvar_mod file gv) ^ ".log")
  | GInv    -> assert false
  | FOpp    -> Oopp
  | FMinus  -> Osub
  | FInv    -> Ostr "F.inv"
  | FDiv    -> Odiv
  | Eq      -> Oeq
  | Not     -> Onot
  | Ifte    -> assert false
  | EMap bm -> Ostr  ((bvar_mod file bm) ^ ".e")

let string_of_nop file ty = function
  | FPlus -> "F.(+)"
  | FMult -> "F.( * )"
  | Xor   -> 
    begin match ty.ty_node with 
    | BS lv -> lvar_mod file lv ^ ".(^)" 
    | Bool  -> assert false
    | _     -> assert false
    end
  | Land -> "(/\\)" 
  | GMult -> gvar_mod file (destr_G ty) ^ ".( * )"

let op_of_nop ty = function
  | FPlus -> Oadd
  | FMult -> Omul
  | Xor   -> 
    begin match ty.ty_node with 
    | BS _ -> Opow
    | Bool  -> assert false
    | _     -> assert false
    end
  | Land -> Oand
  | GMult -> Omul

let string_of_cnst file ty = function
  | GGen   -> fsprintf "%s.g" (gvar_mod file (destr_G ty))
  | FNat i -> fsprintf "(F.ofint %i)" i
  | Z      -> fsprintf "%s.zeros" (lvar_mod file (destr_BS ty))
  | B b    -> fsprintf "%b" b

let rec expression file e = 
  match e.e_node with 
  | InLog(_,_) -> assert false
  | V v -> Epv (pvar [] v)
  | H(h,e) ->  mk_eget file h (expression file e)
  | Tuple es -> Etuple (List.map (expression file) es)
  | Proj (i,e) -> Eproj(i, expression file e) 
  | Cnst c -> Ecnst (string_of_cnst file e.e_ty c)
  | App(Ifte,[e1;e2;e3]) -> 
    Eif(expression file e1, expression file e2, expression file e3)
  | App(op,es) ->
    Eapp(op_of_op file op, List.map (expression file) es)
  | Nary(Land, es) ->
    begin match List.rev es with
    | [] -> assert false
    | e :: es ->
      let op = op_of_nop e.e_ty Land in
      List.fold_left 
        (fun e e1 -> Eapp(op,[expression file e1; e])) 
        (expression file e) es
    end
  | Nary(op,es) -> 
    begin match es with
    | [] -> assert false
    | e::es -> 
      let op = op_of_nop e.e_ty op in
      List.fold_left (fun e e1 -> Eapp(op,[e;expression file e1])) 
        (expression file e) es 
    end
  | Exists _ -> assert false 

let rec formula file prefix mem 
    ?(local=Vsym.S.empty) ?(flocal=Vsym.S.empty) e = 
  match e.e_node with 
  | InLog(_,_) -> assert false
  | V v -> 
    if Vsym.S.mem v flocal then Fv(pvar [] v, None)
    else if Vsym.S.mem v local then Fv (pvar [] v, mem)
    else Fv (pvar prefix v, mem)
  | H(h,e) ->  mk_fget file mem h (formula file prefix mem ~local ~flocal e)
  | Tuple es -> Ftuple (List.map (formula file prefix mem ~local ~flocal) es)
  | Proj (i,e) -> Fproj(i, formula file prefix mem ~local ~flocal e) 
  | Cnst c -> Fcnst (string_of_cnst file e.e_ty c)
  | App(Eq,[e1;e2]) -> 
    f_eq (formula file prefix mem ~local ~flocal e1) 
         (formula file prefix mem ~local ~flocal e2)
  | App(Ifte,[e1;e2;e3]) -> 
    Fif(formula file prefix mem ~local ~flocal e1, 
        formula file prefix mem ~local ~flocal e2, 
        formula file prefix mem ~local ~flocal e3)
  | App(op,es) ->
    Fapp(op_of_op file op, List.map (formula file prefix mem ~local ~flocal) es)
  | Nary(Land, es) ->
    begin match List.rev es with
    | [] -> assert false
    | e :: es ->
      let op = op_of_nop e.e_ty Land in
      List.fold_left 
        (fun e e1 -> Fapp(op,[formula file prefix mem ~local ~flocal e1; e])) 
        (formula file prefix mem ~local ~flocal e) es
    end
  | Nary(op,es) -> 
    begin match es with
    | [] -> assert false
    | e::es -> 
      let op = op_of_nop e.e_ty op in
      List.fold_left 
        (fun e e1 -> Fapp(op,[e;formula file prefix mem ~local ~flocal e1])) 
        (formula file prefix mem ~local ~flocal e) es 
    end
  | Exists _ -> assert false 
  
let rec init_res_expr ty = 
  match ty.ty_node with 
  | BS lv    -> Expr.mk_Z lv
  | Bool     -> Expr.mk_True
  | G gv     -> Expr.mk_GGen gv
  | Fq       -> Expr.mk_FZ
  | Prod tys -> Expr.mk_Tuple (List.map init_res_expr tys)
  | Int      -> assert false

let vc_oracle modn osym = 
  modn, Format.sprintf "c%s" (Osym.to_string osym)

let oracle_info info osym = 
  try Osym.H.find info.adv_g.oinfo osym
  with Not_found -> assert false

let q_oracle_i info osym = 
  try (oracle_info info osym).obound
  with Not_found -> assert false

let q_oracle file osym = 
  let info = adv_info file in
  q_oracle_i info osym

let oracle file (osym,param,lc,ret) = 
  let res = "_res" in
  let vres = [],res in
  let rec body lc = 
    match lc with
    | [] -> [Iasgn([vres], expression file ret)]
    | LLet (v,e) :: lc -> 
      Iasgn ([pvar [] v],expression file e) :: body lc
    | LSamp (v,(ty,r)) :: lc -> 
      Irnd ([pvar [] v], ty, List.map (expression file) r) :: body lc
    | LBind (_vs, _h) :: _ -> assert false 
    (*      while (res <> None && dom <> []) {
            e = hd dom;
            dom = tl dom;
            vs = h.[e];
            body
            } *)
    | LGuard e :: lc-> [Iif (expression file e, body lc, [])] in
  let vc = vc_oracle [] osym in
  let c  = Epv vc in 
  let q  = Ecnst (q_oracle file osym) in 
  let init_res lc = 
    let e = expression file (init_res_expr osym.Osym.codom) in
    [ Iasgn([vres], e);
      Iif (e_lt c q, Iasgn([vc],e_incr c):: lc, []) ] in
  {
    f_name = "o" ^ Osym.to_string osym;
    f_def = Fbody {
    f_param = List.map (fun v -> pvar [] v, v.Vsym.ty) param;
    f_local = (vres, osym.Osym.codom) :: 
      List.map (fun e ->  
        let v = destr_V e in 
        (pvar [] v, v.Vsym.ty)) (Se.elements (write_lcmds lc));
    f_res   = Some (vres, osym.Osym.codom);
    f_body  = init_res (body lc); }
  }

let ginstr file adv = function
  | GLet (v,e) -> Iasgn ([pvar [] v],expression file e)
  | GSamp(v,(ty,r)) -> 
    Irnd ([pvar [] v], ty, List.map (expression file) r)
  | GCall(vs,a,e,_) -> 
    let es = destr_Tuple_nofail e in
    Icall(List.map (pvar []) vs, (adv, "a"^Asym.to_string a),
          List.map (expression file) es)

let instructions file adv gdef =   
  List.map (ginstr file adv) gdef 

module Ass = Assumption
let add_assumption_dec _file _name _assum =
  ()
  (*
  let advty = top_name file ("Adv_"^name) in
  let ngame1 = top_name file ("G_"^name^string_of_int 1) in
  let ngame2 = top_name file ("G_"^name^string_of_int 2) in
  let pub = assum.Ass.ad_pubvars in
  let params = Vsym.S.elements pub in
  let vparams = 
    List.map (fun v -> pvar [] v, v.Vsym.ty) params in

  let game name gdef = 
    let local = 
      Se.fold (fun e l ->
        let v = destr_V e in
        if Vsym.S.mem v pub then l else
        (pvar [] v, v.Vsym.ty) :: l) (gdef_global_vars gdef) [] in 

    let res = ([],"_res") in
    let init = instructions file (mod_name "A" []) gdef in
    let main = {
      f_name = "main";
      f_def = Fbody {
      f_param = [];
      f_local = (res,mk_Bool) :: vparams @ local;
      f_res = Some (res,mk_Bool);
      f_body = 
        init @
          [Icall([res], (mod_name "A" [], "main"), 
                 List.map (fun v -> Epv(pvar [] v)) params)];}
    } in
    { mod_name = name;
      mod_param = ["A", advty];
      mod_body = Mod_def [MCfun main];
    }, List.length init in 

  let g1, len1 = game ngame1 assum.Ass.ad_prefix1 in
  let g2, len2 = game ngame2 assum.Ass.ad_prefix2 in
  let info = {
    ad_name  = assum.Ass.ad_name;
    ad_priv  = assum.Ass.ad_privvars;
    ad_param = params;
    ad_advty = advty;
    ad_cmd1  = g1;
    ad_len1  = len1; 
    ad_cmd2  = g2; 
    ad_len2  = len2;
  } in
  Ht.add file.assump_dec name info
  *)

let add_assumption_comp _file _name _assum =
  ()
  (*
  let advty = top_name file ("Adv_"^name) in
  let ngame = top_name file ("G_"^name) in
  let pub = assum.Ass.ac_pubvars in
  let params = Vsym.S.elements pub in
  let vparams = 
    List.map (fun v -> pvar [] v, v.Vsym.ty) params in

  let game name gdef = 
    let ares = pvar [] assum.Ass.ac_event_var in
    let local = 
      Se.fold (fun e l ->
        let v = destr_V e in
        if Vsym.S.mem v pub then l else
        (pvar [] v, v.Vsym.ty) :: l) (gdef_global_vars gdef) 
        [ares, assum.Ass.ac_event_var.Vsym.ty]
    in 

    let res = ([],"_res") in
    let init = instructions file (mod_name "A" []) gdef in
    let main = {
      f_name = "main";
      f_def = Fbody {
      f_param = [];
      f_local = (res,mk_Bool) :: vparams @ local;
      f_res = Some (res,mk_Bool);
      f_body = 
        init @
          [Icall([ares], (mod_name "A" [], "main"), 
                 List.map (fun v -> Epv(pvar [] v)) params);
           Iasgn([res], expression file assum.Ass.ac_event)];}
    } in
    { mod_name = name;
      mod_param = ["A", advty];
      mod_body = Mod_def [MCfun main];
    }, List.length init in 

  let g, len = game ngame assum.Ass.ac_prefix in
  let info = {
    ac_name  = assum.Ass.ac_name;
    ac_priv  = assum.Ass.ac_privvars;
    ac_param = params;
    ac_advty = advty;
    ac_advret = assum.Ass.ac_event_var.Vsym.ty;
    ac_cmd   = g;
    ac_len   = len; 
  } in
  Ht.add file.assump_comp name info
  *)
  
let add_assumptions file ts = 
  Mstring.iter (fun n a -> add_assumption_dec  file n a) ts.ts_assms_dec;
  Mstring.iter (fun n a -> add_assumption_comp file n a) ts.ts_assms_comp

let init_file ts = 
  let file = empty_file in
  add_lvars    file ts;
  add_gvars    file ts;
  add_bilinears file ts;
  add_hashs     file ts;
  add_assumptions file ts;  
  file


let oracles file oinfo = 
  { mod_name = "O";
    mod_param = [];
    mod_body = Mod_def 
      (List.rev 
      (Osym.H.fold (fun os (oparams,obody,ores) l ->
        MCfun(oracle file (os, oparams, obody, ores))::l) oinfo [])) }

let vc_oracles_i info = 
  Osym.H.fold (fun o _ l -> vc_oracle [] o :: l) info.adv_g.oinfo []  

let vc_oracles file = vc_oracles_i (adv_info file)
   
let game ?(local=`Local) file g = 
  try find_game file g 
  with Not_found ->
    let oinfo = Osym.H.create 7 in
    let add_oinfo (o,params,body,e,_) = 
      Osym.H.add oinfo o (params,body,e) in
    let mk_info i = 
      match i with
      | GCall(_,_,_,odef) -> List.iter add_oinfo odef
      | _ -> () in
    List.iter mk_info g; 
    
    let (nA,tA) = adv_decl file in
    let vcs = vc_oracles file in
    let cdecls = List.map (fun v -> MCvar (v, Type.mk_Int)) vcs in
    let globs = globals g in 
    let m_orcl = oracles file oinfo in
    let alias = (mod_name nA [mod_name "O" []]) in (* FIXME add the H oracle *)
    let m_adv = {
      mod_name = nA;
      mod_param = [];
      mod_body = Mod_alias alias;
    } in
    let init_vcs = List.map (fun v -> Iasgn([v], e_int0)) vcs in
    let f_main = 
      { f_name = "main";
        f_def = Fbody {
        f_param = [];
        f_local = [];
        f_res   = None;
        f_body  = init_vcs @ instructions file (mod_name nA []) g;}
      } in
    let comp = 
      cdecls@globs @ [MCmod m_orcl;
                       MCmod m_adv;
                       MCfun f_main] in
    let name = top_name file "M" in
    let modu = 
      { mod_name  = name;
        mod_param = [nA,tA];
        mod_body  = Mod_def comp;
      } in
    
    bind_game file local g modu;

    modu

let init_section file name pft =
  let name = start_section file name in
  let g = pft.pt_ju.ju_se.se_gdef in
  init_adv_info file g;
  ignore (game ~local:`Global file g);
  name 
  
let extract_pr ?(local=`Local) file mem ju =
  let modm = game ~local file ju.ju_se.se_gdef in
  let modma = {mn = modm.mod_name; ma = [adv_mod file]} in
  let ev   = formula file [modm.mod_name] None ju.ju_se.se_ev in
  Fpr((modma,"main"), mem, [], ev)

let mem = "m"
let cmp_eq = true
let cmp_le = false
let mk_cmp f1 cmp f2 = 
  if cmp = cmp_eq then f_eq f1 f2 else f_le f1 f2
let forall_mem f = Fforall_mem(mem, f)

let add_pr_lemma file f proof = 
  let name = top_name file "Lem" in
  let body = forall_mem f in
  add_local file (Clemma(true, name,body,proof));
  name

let get_game file g = 
  try find_game file g
  with Not_found -> assert false

let pr_admit s _file fmt () =
  F.fprintf fmt "(* %s *) admit." s

let pp_swap nvc side fmt (p,i) = 
  F.fprintf fmt "swap{%i} %i %i" side (nvc + p+1) i

let pp_swaps nvc side fmt sw = 
  if sw <> [] then
    F.fprintf fmt "@[%a.@]@ " (pp_list ";@ " (pp_swap nvc side)) sw

let init_same_ev file ev tac =
  let nA = adv_name file in
  let pp_ev fmt ev = 
    match ev with
    | None -> F.fprintf fmt "_"
    | Some ev -> Printer.pp_form fmt ev in
  let open_pp fmt () = 
    F.fprintf fmt "@[<v>intros &m;byequiv (_: ={glob %s} ==> %a);@ " nA
      pp_ev ev;
    F.fprintf fmt "  [ proc | by [] | by %s].@ " tac in
  let close_pp fmt () = 
    F.fprintf fmt "@]" in
  open_pp,close_pp

let init_same file ju1 ju2 = 
  let g1 = get_game file ju1.ju_se.se_gdef in
  let g2 = get_game file ju2.ju_se.se_gdef in
(*  let ev1 = formula file [g1.mod_name] (Some "1") ju1.ju_ev in  
  let ev2 = formula file [g2.mod_name] (Some "2") ju2.ju_ev in
  let ev  = 
    if cmp = cmp_eq then f_iff ev1 ev2 
    else f_imp ev1 ev2
  in *)
  let ev = None in
  let open_pp, close_pp = 
    init_same_ev file ev "[]" in
  g1, g2, open_pp, close_pp

let pr_swap sw ju1 ju2 file =
  let _,_,open_pp, close_pp = init_same file ju1 ju2 in
  let nvc = List.length (vc_oracles file) in
  fun fmt () ->
    open_pp fmt ();
    pp_swaps nvc 1 fmt sw;
    F.fprintf fmt "sim.";
    close_pp fmt ()

let invert_swap sw = 
  List.fold_left (fun sw (p,i) -> (p+i, -i)::sw) [] sw

type tactic = 
  | Admit
  | Rnd
  | Skip
  | Wp       of int * int
  | Auto
  | Progress of string list
  | Algebra
  | Smt 
  | Call     of form 
  | If
  | Proc
  | Apply    of string
  | Seq      of int * int * form
  | TOr      of tactic list
  | TRepeat  of tactic
  | TSeq     of tactics
  | TSeqSub  of tactic * tactics 
  | Tstring  of string

and tactics = tactic list

type tcommand = 
  | Tac of tactic
  | TSub of tcommands list

and tcommands = tcommand list

let add_auto tacs = 
  match tacs with 
  | Tac Auto :: _ -> tacs 
  | _ -> Tac Auto :: tacs

let add_TSub sub cont = 
  if sub = [] then cont
  else TSub sub :: cont 

let add_wp i1 i2 cont = 
  match cont with
  | Tac (Wp(i1',i2')) :: _ | Tac (TSeq (Wp(i1',i2')::_)) :: _ ->
    assert (i1' <= i1);
    assert (i2' <= i2);
    cont
  | Tac ((Rnd | Skip | If) as t1) :: cont ->
    Tac (TSeq [Wp(i1,i2);t1]) :: cont
  | Tac (TSeq ts) :: cont ->
    Tac (TSeq (Wp(i1,i2)::ts)) :: cont
  | _ -> Tac(Wp(i1,i2)) :: cont


let add_rnd cont = 
  match cont with
  | Tac ((Rnd | Skip | Wp _ | If) as t1) :: cont ->
    Tac (TSeq [Rnd;t1]) :: cont
  | Tac (TSeq ts) :: cont ->
    Tac (TSeq (Rnd::ts)) :: cont
  | _ -> Tac Rnd :: cont

let t_algebra = TSeq[Algebra; 
                     Tstring 
                       "rewrite ?supp_def ?FSet.mem_single;progress;algebra *";
                     Smt]
let t_spa = TSeq [Skip;Progress [];t_algebra]
let t_apa = TSeq [Auto;Progress [];t_algebra]
let t_pa  = TSeq [Progress [];t_algebra]
let t_aa  = TSeq [Auto;t_algebra]
let t_id  = TSeq []

let t_pr_if = 
  Tstring "by progress;algebra *;smt"


let rec pp_tac fmt = function
  | Admit     -> F.fprintf fmt "admit" 
  | Rnd       -> F.fprintf fmt "rnd" 
  | Skip      -> F.fprintf fmt "skip"
  | Wp(i1,i2) -> F.fprintf fmt "wp %i %i" i1 i2
  | Auto      -> F.fprintf fmt "auto" 
  | Progress s-> 
    if s = [] then F.fprintf fmt "progress" 
    else 
      F.fprintf fmt "progress @[[%a]@]" 
        (pp_list "@ " (fun fmt -> F.fprintf fmt "%s")) s
  | Algebra   -> F.fprintf fmt "algebra *"
  | Smt       -> F.fprintf fmt "smt"
  | Call inv  -> F.fprintf fmt "call (_:%a)" Printer.pp_form inv
  | If        -> F.fprintf fmt "if" 
  | Proc      -> F.fprintf fmt "proc"
  | Seq (i1,i2,f) -> 
    F.fprintf fmt "@[seq %i %i :@ (@[%a@])@]" i1 i2 Printer.pp_form f
  | Apply s   -> F.fprintf fmt "apply %s" s
  | TOr []    -> ()
  | TOr [t]   -> pp_tac fmt t
  | TOr ts    -> 
    F.fprintf fmt "(@[%a@])" (pp_list " ||@ " pp_tac) ts
  | TRepeat t -> F.fprintf fmt "do ?%a" pp_tac t
  | TSeq lt   -> 
    if lt <> [] then
      F.fprintf fmt "@[<hov>(%a)@]" (pp_list ";@ " pp_tac) lt 
  | TSeqSub(t, ts) ->
    F.fprintf fmt "@[<hov 2>%a;@ [ @[<hov 0>%a@]]@]" 
      pp_tac t
      (pp_list " |@ " pp_tac) ts
  | Tstring s -> F.fprintf fmt "%s" s


let rec pp_cmd fmt = function
  | Tac (TSeq lt) ->
    if lt <> [] then
      F.fprintf fmt "@[<hov>%a.@]" (pp_list ";@ " pp_tac) lt 
  | Tac t -> F.fprintf fmt "%a." pp_tac t
  | TSub ts -> 
    F.fprintf fmt "  @[<v>%a@]" 
      (pp_list "@ @ " pp_cmds) ts
      
and pp_cmds fmt tacs=
  F.fprintf fmt "@[<v>%a@]" (pp_list "@ " pp_cmd) tacs 



type conv_info = {
  loc1 : Vsym.S.t;
  loc2 : Vsym.S.t;
  pos1 : int;
  pos2 : int;
  tacs : tcommands;
  invs : form
}

let add_let_info file g v e side loc info = 
  let s = if side then Some "1" else Some "2" in
  let loc1 = if side && loc then Vsym.S.add v info.loc1 else info.loc1 in
  let loc2 = if not side && loc then Vsym.S.add v info.loc2 else info.loc2 in
  let local = if side then loc1 else loc2 in
  let e1 = formula file [g.mod_name] s ~local e in
  let e2 = formula file [g.mod_name] s ~local (Expr.mk_V v) in
  { 
    loc1 = loc1;
    loc2 = loc2;
    pos1 = if side then info.pos1 + 1 else info.pos1;
    pos2 = if side then info.pos2 else info.pos2 + 1;
    tacs = add_wp info.pos1 info.pos2 info.tacs;
    invs = f_and (f_eq e1 e2) info.invs }

let add_rnd_info file g1 g2 v1 v2 l1 l2 loc info = 
  let loc1 = if loc then Vsym.S.add v1 info.loc1 else info.loc1 in
  let loc2 = if loc then Vsym.S.add v2 info.loc2 else info.loc2 in
  let e1 = formula file [g1.mod_name] (Some "1") ~local:loc1 (Expr.mk_V v1) in
  let e2 = formula file [g2.mod_name] (Some "2") ~local:loc2 (Expr.mk_V v2) in
  let add_restr side e l invs = 
    let g,s,local = 
      if side then g1.mod_name, Some "1", loc1
      else g2.mod_name, Some "2", loc2 in
    let l = List.map (formula file [g] s ~local) l in
    List.fold_left (fun invs e' -> f_and (f_neq e e') invs) invs l in
  let invs = add_restr true e1 l1 info.invs in
  let invs = add_restr false e2 l2 invs in
  { loc1 = loc1;
    loc2 = loc2;
    pos1 = info.pos1 + 1;
    pos2 = info.pos2 + 1;
    tacs = add_rnd info.tacs;
    invs = f_and (f_eq e1 e2) invs }

let add_guard file g1 g2 e1 e2 info tacs =
  let e1 = formula file [g1.mod_name] (Some "1") ~local:info.loc1 e1 in
  let e2 = formula file [g2.mod_name] (Some "2") ~local:info.loc2 e2 in 
  let t = f_and e1 e2 in
  { 
    loc1 = info.loc1;
    loc2 = info.loc2;
    pos1 = 0;
    pos2 = 0;
    tacs = tacs; 
    invs = f_and t info.invs } 
  
let init_inv_oracle p1 p2 inv =
  let add_eq f v1 v2 = 
    f_and (f_eq (Fv(pvar [] v1, Some "1")) (Fv(pvar [] v2, Some "2"))) f in
  List.fold_left2 add_eq 
    (f_and (f_eq (Fv(([],"_res"), Some "1")) (Fv(([],"_res"), Some "2"))) inv)
    p1 p2

(*let mk_eq_ *)
let mk_eq_expr_p file ?(local=Vsym.S.empty) p1 p2 e = 
  f_eq 
    (formula file [p1] (Some "1") ~local e)
    (formula file [p2] (Some "2") ~local e)

let mk_eq_expr file ?(local=Vsym.S.empty) g1 g2 e =
  mk_eq_expr_p file ~local g1.mod_name g2.mod_name e

let mk_eq_exprs_p file ?(local=Vsym.S.empty) p1 p2 es =
  match Se.elements es with
  | [] -> f_true
  | e::es -> 
    List.fold_left (fun eq e -> f_and eq (mk_eq_expr_p file ~local p1 p2 e))
      (mk_eq_expr_p file ~local p1 p2 e) es
  
let mk_eq_exprs file ?(local=Vsym.S.empty) g1 g2 es =
  mk_eq_exprs_p file ~local g1.mod_name g2.mod_name es

let mk_eq_vcs g1 g2 vcs = 
  match vcs with
  | [] -> f_true
  | v::vs ->
    let mk_eq v = f_eq (f_v g1 v "1") (f_v g2 v "2") in
    List.fold_left (fun eq v -> f_and eq (mk_eq v)) (mk_eq v) vs 

let pp_inv file ?(local=Vsym.S.empty) g fmt (x,inv) = 
  let flocal = Vsym.S.singleton x in
  let f = formula file [g.mod_name] (Some "2") ~local ~flocal inv in
  F.fprintf fmt "@[<hov 2>(fun (%a:%a),@ %a)@]"
    Vsym.pp x (Printer.pp_type file) x.Vsym.ty Printer.pp_form f 

let mu_x_def file fmt ty = 
  match ty.ty_node with
  | BS lv -> 
    F.fprintf fmt "%a.Dword.mu_x_def" Printer.pp_mod_name (mod_lvar file lv)
  | Bool ->
    F.fprintf fmt "Bool.Dbool.mu_x_def"
  | G _gv -> assert false (* FIXME *)
  | Fq    -> F.fprintf fmt "FDistr.mu_x_def_in"
  | Prod _ -> assert false (* FIXME *) 
  | Int -> assert false

let supp_def file fmt ty = 
  match ty.ty_node with
  | BS lv -> 
    F.fprintf fmt "%a.Dword.in_supp_def" Printer.pp_mod_name (mod_lvar file lv)
  | Bool ->
    F.fprintf fmt "Bool.Dbool.supp_def"
  | G _gv -> assert false (* FIXME *)
  | Fq    -> F.fprintf fmt "FDistr.supp_def"
  | Prod _ -> assert false (* FIXME *) 
  | Int -> assert false

let build_conv_proof nvc eqvc file g1 g2 lc1 lc2 = 
  let add_info1 v1 e1 loc info = 
    add_let_info file g1 v1 e1 true loc info in
  let add_info2 v2 e2 loc info = 
    add_let_info file g2 v2 e2 false loc info in
  let add_rnd v1 v2 l1 l2 loc info = 
    add_rnd_info file g1 g2 v1 v2 l1 l2 loc info in
  let prove_orcl info (o1,p1,lc1,_,_) (o2,p2,lc2,_,_) =
    let rec aux lc1 lc2 info = 
      match lc1, lc2 with
      | [], [] -> add_wp info.pos1 info.pos2 info.tacs
      | LLet (v1,e1)::lc1, _ ->
        aux lc1 lc2 (add_info1 v1 e1 true info)
      | _, LLet (v2,e2)::lc2 ->
        aux lc1 lc2 (add_info2 v2 e2 true info)
      | LSamp(v1,(_,l1))::lc1, LSamp(v2,(_,l2))::lc2 ->
        aux lc1 lc2 (add_rnd v1 v2 l1 l2 true info) 
      | LBind _ :: _, LBind _ :: _ -> assert false (* FIXME *)
      | LGuard e1 :: lc1, LGuard e2 :: lc2 ->
        let tacs = aux lc1 lc2 (add_guard file g1 g2 e1 e2 info [Tac t_spa]) in
        if info.pos1 = 0 && info.pos2 = 0 then 
          Tac (TSeqSub(If, [t_pr_if; t_id; t_aa])) :: tacs 
        else
          Tac (Seq (info.pos1, info.pos2, info.invs)) ::
            TSub [info.tacs] ::
            Tac (TSeqSub(If, [t_pr_if; t_id; t_aa])) ::
            tacs 
      | _, _ -> assert false in
    let inv = init_inv_oracle p1 p2 info.invs in
    let info = 
      { loc1 = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p1;
        loc2 = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p2;
        pos1 = 0; pos2 = 0;
        tacs = [Tac t_spa];
        invs  = inv } in
    let tacs = aux lc1 lc2 info in
    let no1 = snd (vc_oracle [] o1) in
    let no2 = snd (vc_oracle [] o2) in
    Tac (Tstring "proc;sp 1 1;if;[by done | | by done]") :: 
    Tac (Tstring (Format.sprintf "sp 1 1;elim * => %s_R %s_L" no1 no2)) ::
    tacs in
        
  let add_call vs1 odef1 vs2 odef2 info = 
    let prove_orcl o1 o2 = prove_orcl info o1 o2 in
    let mk_eq v1 v2 = 
      let e1 = formula file [g1.mod_name] (Some "1") (Expr.mk_V v1) in
      let e2 = formula file [g2.mod_name] (Some "2") (Expr.mk_V v2) in 
      f_eq e1 e2 in
    let eqs = List.map2 mk_eq vs1 vs2 in
    let pr_orcls = List.map2 prove_orcl odef1 odef2 in
    { loc1 = info.loc1;
      loc2 = info.loc2;
      pos1 = info.pos1 + 1;
      pos2 = info.pos2 + 1;
      tacs = Tac (Call info.invs) :: TSub pr_orcls :: info.tacs;
      invs = List.fold_left (fun f eq -> f_and eq f) info.invs eqs } in
  (* the game are now ju ju' *)
  (* collect the distributions *)
  let ds = ref Sty.empty in
  let rec aux lc1 lc2 info = 
    match lc1, lc2 with
    | [], [] -> info
    | GLet (v1,e1)::lc1, _ ->
      aux lc1 lc2 (add_info1 v1 e1 false info)
    | _, GLet (v2,e2)::lc2 ->
      aux lc1 lc2 (add_info2 v2 e2 false info)
    | GSamp(v1,(ty,l1))::lc1, GSamp(v2,(_,l2))::lc2 ->
      if l1 <> [] then ds := Sty.add ty !ds;
      aux lc1 lc2 (add_rnd v1 v2 l1 l2 false info) 
    | GCall(vs1,_,_,odef1)::lc1, GCall(vs2,_,_,odef2)::lc2 ->
      aux lc1 lc2 (add_call vs1 odef1 vs2 odef2 info)
    | _, _ -> assert false in
  let info = 
    { loc1 = Vsym.S.empty; loc2 = Vsym.S.empty;
      pos1 = nvc; pos2 = nvc;
      tacs = []; invs = eqvc } in
  let info = aux lc1 lc2 info in
  let t_end = 
    let ts = 
      Sty.fold (fun ty l ->
        F.fprintf F.str_formatter
          "by apply (in_excepted_diff %a)" 
            (Printer.pp_ty_distr file) ty;
        let s = F.flush_str_formatter () in
        Tstring s :: l) !ds [Tstring "by algebra *" ] in
    if ts = [] then [] else [TOr ts] in
  { info with 
    tacs = info.tacs @ [Tac (TSeq (Auto::Progress []::t_end))] }

let pr_conv sw1 ju1 ju ju' ju2 sw2 file = 
  let g1 = get_game file ju1.ju_se.se_gdef in
  let g2 = get_game file ju2.ju_se.se_gdef in
  let vcs = vc_oracles file in
  let eqvc = mk_eq_vcs g1 g2 vcs in
  let nvc = List.length vcs in
  let info = build_conv_proof nvc eqvc file g1 g2 ju.ju_se.se_gdef ju'.ju_se.se_gdef in 
  let open_pp, close_pp = 
    init_same_ev file (Some info.invs) "progress;algebra*" in
  fun fmt () -> 
    open_pp fmt (); 
    F.fprintf fmt "(* conv rule *)@ ";
    pp_swaps nvc 1 fmt sw1;
    pp_swaps nvc 2 fmt (invert_swap sw2);
    pp_cmds fmt info.tacs;
    close_pp fmt ()

let pr_random (pos,inv1,inv2) ju1 ju2 file =
  let g1,g2,open_pp, close_pp = init_same file ju1 ju2 in
  let vcs = vc_oracles file in
  let nvc = List.length vcs in
  let eqvc = mk_eq_vcs g1 g2 vcs in
  let npos = pos + nvc in
  let lc1 = Util.take pos ju1.ju_se.se_gdef in
  let lc2 = Util.take pos ju2.ju_se.se_gdef in

  let info = build_conv_proof nvc eqvc file g1 g2 lc1 lc2 in 
  let nA = adv_name file in
  fun fmt () ->
    open_pp fmt ();
    F.fprintf fmt "sim.@ ";
    F.fprintf fmt "wp %i %i.@ " (npos + 1) (npos + 1);
    F.fprintf fmt "@[<hov 2>rnd@ %a@ %a.@]@ "
      (pp_inv file g2) inv2 (pp_inv file g2) inv1;
    F.fprintf fmt "@[<hov 2>conseq (_: _ ==>@ %a /\\ ={glob %s}).@]@ " 
      Printer.pp_form (f_and info.invs eqvc) nA;
    let ty = (fst inv1).Vsym.ty in 
    F.fprintf fmt "  progress.@ ";
    F.fprintf fmt "    by algebra *.@ ";
    F.fprintf fmt "    by rewrite !%a.@ " (mu_x_def file) ty;
    F.fprintf fmt "    by apply %a.@ " (supp_def file) ty;
    F.fprintf fmt "    by algebra *.@ ";
    pp_cmds fmt info.tacs;
    close_pp fmt ()

let pr_random_orcl (pos, inv1, inv2) ju1 ju2 file =
  let g1,g2,open_pp, close_pp = init_same file ju1 ju2 in
  let vcs = vc_oracles file in
  let eqvc = mk_eq_vcs g1 g2 vcs in
  let nvc = List.length vcs in
  let se1 = ju1.ju_se in
  let se2 = ju2.ju_se in

  let _i, ctxt = Game.get_se_octxt se1 pos in
  let _i, ctxt2 = Game.get_se_octxt se2 pos in
  let jctxt = ctxt.seoc_sec in
  let write1 = write_gcmds jctxt.sec_left in
  let writec = add_binding ctxt.seoc_avars in
  let write1c = Se.union write1 writec in
  let write2 = write_gcmds jctxt.sec_right in
  let write = Se.union write1c write2 in
  (* The proof of the oracle *)
  let ginv = f_and (mk_eq_exprs file g1 g2 write1) eqvc in
  let p1 = ctxt.seoc_oargs and p2 = ctxt2.seoc_oargs in
  let iinv = init_inv_oracle p1 p2 ginv in
  let add_info1 v1 e1 loc info = 
    add_let_info file g1 v1 e1 true loc info in
  let add_info2 v2 e2 loc info = 
    add_let_info file g2 v2 e2 false loc info in
  let add_rnd v1 v2 loc info = add_rnd_info file g1 g2 v1 v2 loc info in
  let rec aux lc1 lc2 info = 
    match lc1, lc2 with
    | [], [] -> info
    | LLet (v1,e1)::lc1, _ ->
      aux lc1 lc2 (add_info1 v1 e1 true info)
    | _, LLet (v2,e2)::lc2 ->
      aux lc1 lc2 (add_info2 v2 e2 true info)
    | LSamp(v1,(_,l1))::lc1, LSamp(v2,(_,l2))::lc2 ->
      aux lc1 lc2 (add_rnd v1 v2 l1 l2 true info) 
    | LBind _ :: _, LBind _ :: _ -> assert false (* FIXME *)
    | LGuard e1 :: lc1, LGuard e2 :: lc2 ->
      let info' = aux lc1 lc2 (add_guard file g1 g2 e1 e2 info []) in
      let tacs = 
        if info.pos1 = 0 && info.pos2 = 0 then 
          Tac (TSeqSub(If, [t_pr_if; t_id; t_aa])) :: info'.tacs 
        else
          Tac (Seq (info.pos1, info.pos2, info.invs)) ::
            TSub [info.tacs] ::
            Tac (TSeqSub(If, [t_pr_if; t_id; t_aa])) ::
            info'.tacs in
      { info' with tacs = tacs }
    | _, _ -> assert false in
  let info = 
    { loc1 = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p1;
      loc2 = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p2;
      pos1 = 0; pos2 = 0;
      tacs = [];
      invs  = iinv } in
  let info = aux ctxt.seoc_cleft ctxt2.seoc_cleft info in
  let nA = adv_name file in
  fun fmt () ->
    (* FIXME use init_same_ev as in pr_rw_oracle *)
    open_pp fmt ();
    F.fprintf fmt "conseq (_: _ ==> @[%a@]) => //.@ "
      Printer.pp_form (mk_eq_exprs file g1 g2 write);
    let len = nvc + List.length jctxt.sec_left in

    F.fprintf fmt "seq %i %i : (@[={glob A} /\\ %a@]);@ " len len
      Printer.pp_form ginv;
    F.fprintf fmt "  [ by sim | ].@ ";
    if jctxt.sec_right <> [] then begin
      F.fprintf fmt "seq %i %i : (@[={glob %s} /\\ %a@]);@ " 
        1 1 nA
        Printer.pp_form  (f_and (mk_eq_exprs file g1 g2 write1c) eqvc);
      F.fprintf fmt "  [ | by sim ].@ "
    end;

    F.fprintf fmt "call (_: @[%a@]).@ "
      Printer.pp_form ginv;
    List.iter (fun _ -> F.fprintf fmt "  by sim.@ ") ctxt.seoc_oleft;
    (* Start proof of the oracle *)
    F.fprintf fmt "  proc;sp 1 1;if;[by done | | by done].@ ";
    F.fprintf fmt "  seq 1 1 : (@[%a@]);[by sim | ].@ "
      Printer.pp_form iinv;
    F.fprintf fmt "  @[%a@]@ " pp_cmds info.tacs;
    F.fprintf fmt "  sim.@ ";
    F.fprintf fmt "  wp 1 1.@ ";
    F.fprintf fmt "  @[<hov 2>rnd@ %a@ %a.@]@ "
      (pp_inv file ~local:info.loc2 g2) inv2 (pp_inv file ~local:info.loc2 g2)
      inv1;
    F.fprintf fmt "  @[<hov 2>conseq (_: _ ==>@ %a).@]@ " 
      Printer.pp_form info.invs;
    let ty = (fst inv1).Vsym.ty in 
    F.fprintf fmt "    progress.@ ";
    F.fprintf fmt "      by algebra *.@ ";
    F.fprintf fmt "      by rewrite !%a.@ " (mu_x_def file) ty;
    F.fprintf fmt "      by apply %a.@ " (supp_def file) ty;
    F.fprintf fmt "      by algebra *.@ ";
    F.fprintf fmt "    auto.@ ";
    
    (* End proof of the oracle *)
    List.iter (fun _ -> F.fprintf fmt "  by sim.@ ") ctxt.seoc_oright;
    F.fprintf fmt "auto.";
    close_pp fmt ()
  
  
let pr_rw_orcl ((i,_oi,_j) as op,dir) ju1 ju2 file = 
  let g1, g2, open_pp, close_pp = init_same file ju1 ju2 in
  let vcs = vc_oracles file in
  let eqvc = mk_eq_vcs g1 g2 vcs in
  let nvc = List.length vcs in

  let se1 = ju1.ju_se in
  let lg, se_o = Game.get_se_octxt se1 op in
  let n1 = nvc + List.length se_o.seoc_sec.sec_left in
  let w1 = Game.write_gcmds (List.rev se_o.seoc_sec.sec_left) in
  let ev1 = f_and eqvc (mk_eq_exprs file g1 g2 w1) in
  let gc, _ = Game.get_se_ctxt se1 i in
  let w2 = Se.union w1 (Game.write_gcmd gc) in
  let ev2 = f_and eqvc (mk_eq_exprs file g1 g2 w2) in
  let nA = adv_name file in
  let pp_invA fmt ev = 
    F.fprintf fmt "={glob %s} /\\ %a" nA Printer.pp_form ev in
  let add_bind_info add_tac v info =
    let loc1 = Vsym.S.add v info.loc1 in
    let loc2 = Vsym.S.add v info.loc2 in
    let e1 = formula file [g1.mod_name] (Some "1") ~local:loc1 (Expr.mk_V v) in
    let e2 = formula file [g2.mod_name] (Some "2") ~local:loc2 (Expr.mk_V v) in
    { loc1 = loc1;
      loc2 = loc2;
      pos1 = info.pos1 + 1;
      pos2 = info.pos2 + 1;
      tacs = add_tac info.tacs;
      invs = f_and info.invs (f_eq e1 e2) } in
  let add_let_info v info =
    add_bind_info (add_wp info.pos1 info.pos2) v info in
  let add_rnd_info v info = 
    add_bind_info add_rnd v info in
  let t_bydone = Tstring "by done" in
  let rec aux lc info = 
    match lc with
    | [] -> info
    | LLet(v,_) :: lc ->
      aux lc (add_let_info v info)
    | LSamp(v,_):: lc ->
      aux lc (add_rnd_info v info)
    | LBind _ :: _ -> assert false
    | LGuard _e :: lc ->
      let info' = aux lc info in
      let tacs = 
        if info.pos1 = 0 && info.pos2 = 0 then 
          Tac (TSeqSub(If, [t_bydone; t_id; t_bydone])) :: info'.tacs 
        else
          Tac (Seq (info.pos1, info.pos2, info.invs)) ::
            TSub [info.tacs] ::
            Tac (TSeqSub(If, [t_bydone; t_id; t_bydone])) ::
            info'.tacs in
      { info with tacs = tacs } in
  
  let p1 = se_o.seoc_oargs in
  let iinv = init_inv_oracle p1 p1 ev1 in
  let loc = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p1 in
  let info0 = 
    { loc1 = loc; loc2 = loc;
      pos1 = 0; pos2 = 0;
      tacs = []; invs  = iinv } in
  let info1 = aux se_o.seoc_cleft info0 in

  let t_end n = 
    let rec pp_intro n =
      if n = 0 then Format.sprintf "[H1 H2]" 
      else Format.sprintf "[%s H%i]" (pp_intro (n-1)) (n+2) in
    let rec pp_gen n = 
      if n =0 then ""
      else Format.sprintf "H%i %s" (n+2) (pp_gen (n-1)) in
    let s = 
      Format.sprintf "by move=> &m1 &m2 %s;move: H1 %s;rewrite %sH2"
        (pp_intro n) (pp_gen n) 
        (if dir = LeftToRight then "" else "-")
     in
    Tstring s in


  let rec aux2 nend n lc info =
    match lc with
    | [] -> info.tacs @ [Tac (TSeq [Auto; (t_end nend)])]
    | LLet(v,_) :: lc ->
      aux2 nend (n+1) lc (add_let_info v info)
    | LSamp(v,_):: lc ->
      aux2 nend (n+1) lc (add_rnd_info v info)
    | LBind _ :: _ -> assert false
    | LGuard e :: lc ->
      if info.pos1 = 0 && info.pos2 = 0 then
         Tac (TSeqSub(If, [t_end nend; t_id; t_bydone]))::
         aux2 (nend+1) (n+1) lc (add_guard file g1 g2 e e info [])
      else
         Tac (Seq (info.pos1, info.pos2, info.invs)) ::
         TSub ([info.tacs; [Tac (TSeq [Skip; t_end nend])]]) ::
         Tac (TSeqSub(If, [t_end n; t_id; t_bydone]))::
         aux2 (n+1) (n+1) lc (add_guard file g1 g2 e e info []) in

  let cond = match lg with LGuard t -> t | _ -> assert false in
  let info2 = add_guard file g1 g2 cond cond info1 [] in
  let tac_end = aux2 0 0 se_o.seoc_cright info2 in 
  fun fmt () ->
    open_pp fmt ();
    F.fprintf fmt "(* Rewrite oracle *)@ ";
    F.fprintf fmt "seq %i %i : (%a); first by sim.@ " n1 n1 pp_invA ev1;
    if se_o.seoc_sec.sec_right <> [] then
      F.fprintf fmt "seq 1 1 : (%a); last by sim.@ " pp_invA ev2;
    F.fprintf fmt "call (_: %a);last by done.@ " Printer.pp_form ev1;
    (* Proof of oracles *)
    let pp_other fmt os =
      pp_list "" (fun fmt _ -> F.fprintf fmt "  by sim.@ ") fmt os in
    pp_other fmt se_o.seoc_oleft;
    F.fprintf fmt "  proc;sp 1 1;if;[ by done | | by done].@ ";
    F.fprintf fmt "  %a" pp_cmds 
      [Tac (TSeqSub (Seq(1, 1, iinv), [Auto; t_id]))];
    F.fprintf fmt "  %a@ " pp_cmds info1.tacs;
    F.fprintf fmt "  if;[by done | | by done].@ ";
    F.fprintf fmt "  @[<v>%a@]" pp_cmds tac_end;
    pp_other fmt se_o.seoc_oright;
    close_pp fmt ()



  

let pr_intr_rw1_app lemma1 lemma2 fmt () = 
  F.fprintf fmt "intros &m; rewrite {1}(%s &m);apply (%s &m)."
    lemma1 lemma2 

let extract_assum file dir subst ainfo pft pft' =
  let g  = game file pft.pt_ju.ju_se.se_gdef in
  let g'  = game file pft'.pt_ju.ju_se.se_gdef in
  let nvc = List.length (vc_oracles file) in

  let ev = pft.pt_ju.ju_se.se_ev in
  let len = if dir = LeftToRight then ainfo.ad_len1 else ainfo.ad_len2 in
  let fadv =
    let comp = match g.mod_body with 
      | Mod_def cmp -> cmp 
      | _ -> assert false in
    let comp, f = 
      match List.rev comp with 
      | MCfun f :: r -> List.rev r, f
      | _ -> assert false in
    let subst_v (x:Vsym.t) = try Vsym.M.find x subst with Not_found -> x in
    let priv = 
      Vsym.S.fold (fun v p -> Sstring.add (Vsym.to_string (subst_v v)) p)
        ainfo.ad_priv Sstring.empty in
    (* The private variables should be remove *)
    let tokeep = function
      | MCvar ((_,v),_) -> not (Sstring.mem v priv) 
      | _ -> true in
    let comp = List.filter tokeep comp in
    let main = 
      let mk_param v = 
        (([], "_" ^ Vsym.to_string v), v.Vsym.ty) in
      let param = List.map mk_param ainfo.ad_param in
      let glob = List.map subst_v ainfo.ad_param in
      let assign_global = 
        List.map2 (fun vg (v,_) -> Iasgn([pvar [] vg], Epv v)) glob param in
      let res = ([], "_res") in
      let dres = res, mk_Bool in
      let ev = expression file ev in
      let init_vc, main = Util.cut_n nvc (f_body f) in 
      { f_name = "main";
        f_def = Fbody {
        f_param = param;
        f_local = [dres];
        f_res   = Some dres;
        f_body  = 
          assign_global @ 
            (* The head should be remove *)
            List.rev_append init_vc
            (drop len main @ [Iasgn([res], ev)]) } }in
    let advname = top_name file ("Fadv_"^ainfo.ad_name) in 
    { mod_name = advname;
      mod_param = g.mod_param;
      mod_body = Mod_def (comp @ [MCfun main]) } in
  add_game file `Top fadv;
(*  file.glob_decl <- Cmod fadv :: file.glob_decl; *)
  let fa = mod_name fadv.mod_name [mod_name (adv_name file) []] in
  let a1 = mod_name ainfo.ad_cmd1.mod_name [fa] in
  let a2 = mod_name ainfo.ad_cmd2.mod_name [fa] in
  let pr = extract_pr file mem pft.pt_ju in
  let pr' = extract_pr file mem pft'.pt_ju in
  let pra1 = Fpr((a1,"main"), mem, [], Fv(([],"res"),None)) in
  let pra2 = Fpr((a2,"main"), mem, [], Fv(([],"res"),None)) in
  let pra, pra' = if dir = LeftToRight then pra1, pra2 else pra2, pra1 in
  let nA = adv_name file in
  let proof_ass g ev = 
    let ev = formula file [g.mod_name] (Some "1") ev in
    fun fmt () -> 
    F.fprintf fmt 
      "@[<v> intros &m; byequiv (_: @[={glob %s} ==>@ %a@]) => //.@ " nA
      Printer.pp_form (f_eq ev (Fv(([], "res"), Some "2")));
    F.fprintf fmt
      "by proc; inline{2} %a; wp => /=; sim;auto.@]"
      Printer.pp_fun_name (fa,"main") in
  let lemma = 
    add_pr_lemma file (mk_cmp pr cmp_eq pra) 
      (Some (proof_ass g pft.pt_ju.ju_se.se_ev)) in
  let lemma' = 
    add_pr_lemma file (mk_cmp pr' cmp_eq pra') 
      (Some (proof_ass g' pft'.pt_ju.ju_se.se_ev)) in
  let abs = Fabs (f_rsub pra1 pra2) in
  let proof fmt () = 
    F.fprintf fmt 
      "intros &m;rewrite (%s &m) (%s &m);apply ZooUtil.le_abs_add%i."  
      lemma lemma' (if dir = LeftToRight then 1 else 2) in
  let concl = 
    add_pr_lemma file 
      (mk_cmp pr cmp_le (f_radd abs pr'))
      (Some proof) in
  concl, pr, abs 

let extract_assum_comp _file _subst _ainfo _ranges _pft =
  (*
  let g  = game file pft.pt_ju.ju_se.se_gdef in
  let nvc = List.length (vc_oracles file) in

  let len = ainfo.ac_len in
  let fadv =
    let comp = match g.mod_body with 
      | Mod_def cmp -> cmp 
      | _ -> assert false in
    let comp, f = 
      match List.rev comp with 
      | MCfun f :: r -> List.rev r, f
      | _ -> assert false in
    let subst_v (x:Vsym.t) = try Vsym.M.find x subst with Not_found -> x in
    let priv = 
      Vsym.S.fold (fun v p -> Sstring.add (Vsym.to_string (subst_v v)) p)
        ainfo.ac_priv Sstring.empty in
    (* The private variables should be remove *)
    let tokeep = function
      | MCvar ((_,v),_) -> not (Sstring.mem v priv) 
      | _ -> true in
    let comp = List.filter tokeep comp in
    let main = 
      let mk_param v = 
        (([], "_" ^ Vsym.to_string v), v.Vsym.ty) in
      let param = List.map mk_param ainfo.ac_param in
      let glob = List.map subst_v ainfo.ac_param in
      let assign_global = 
        List.map2 (fun vg (v,_) -> Iasgn([pvar [] vg], Epv v)) glob param in
      let res = ([], "_res") in
      let dres = res, ainfo.ac_advret in
      let ev = expression file expr in
      let init_vc, main = Util.cut_n nvc (f_body f) in 
      { f_name = "main";
        f_def = Fbody {
        f_param = param;
        f_local = [dres];
        f_res   = Some dres;
        f_body  = 
          assign_global @ 
            (* The head should be remove *)
            List.rev_append init_vc
            (drop len main @ [Iasgn([res], ev)]) } } in
    let advname = top_name file ("Fadv_"^ainfo.ac_name) in 
    { mod_name = advname;
      mod_param = g.mod_param;
      mod_body = Mod_def (comp @ [MCfun main]) } in
  add_game file `Top fadv;
  let fa = mod_name fadv.mod_name [mod_name (adv_name file) []] in
  let a = mod_name ainfo.ac_cmd.mod_name [fa] in
  let pr = extract_pr file mem pft.pt_ju in
  let pra = Fpr((a,"main"), mem, [], Fv(([],"res"),None)) in
  let nA = adv_name file in
  let proof_ass = 
    fun fmt () -> 
      F.fprintf fmt "(* Assumption computational *)@ ";
      F.fprintf fmt 
        "@[<v>intros &m; byequiv (_: @[={glob %s} ==>@ _@]) => //.@ " nA;
      F.fprintf fmt
        "by proc; inline{2} %a; wp => /=; sim;auto.@]"
        Printer.pp_fun_name (fa,"main") in
  let lemma = 
    add_pr_lemma file (mk_cmp pr cmp_eq pra) (Some proof_ass) in
  lemma, pr, cmp_eq, pra
  *)
  ()

let rec skip_conv pft = 
  match pft.pt_rule with
  | Rconv -> skip_conv (List.hd pft.pt_children)
  | _ -> pft

let skip_swap pft = 
  let rec aux sw pft = 
    match pft.pt_rule with
    | Rswap(p,i) -> aux ((p,i)::sw) (List.hd pft.pt_children)
    | _ -> List.rev sw, pft in
  aux [] pft

let bound_rnd_indep file pos ju = 
  let ty,l = 
    match List.rev ju.ju_se.se_gdef with GSamp(_,d) :: _ -> d | _ -> assert false in
  let size, lemma =
    match ty.ty_node with
    | BS lv -> f_2pow (bs_length file lv), lvar_mod file lv ^".Dword.mu_x_def"
    | Bool  -> f_2  , "Bool.Dbool.mu_x_def"
    | G _   -> f_Fq,  assert false (* FIXME *)
    | Fq    -> f_Fq,  "FDistr.mu_x_def_in"
    | _     -> assert false (* FIXME *) in
  let isize = f_rinv (Frofi size) in
  assert (l = []);
  let evs = destr_Land_nofail ju.ju_se.se_ev in
  let ev = List.nth evs pos in
  if is_Eq ev then isize, ev, lemma 
  else assert false (* FIXME exists *)

let extract_rnd_indep file side pos ju = 
  let g = game file ju.ju_se.se_gdef in
  let pr = extract_pr file mem ju in
  let bound, ev, lemma = bound_rnd_indep file pos ju in
  let proof fmt () =
    F.fprintf fmt "(* Random indep *)@ ";
    F.fprintf fmt "@[<v>intros &m; byphoare (_ : ) => //.@ "
      (* Printer.pp_form (formula file [g.mod_name] None ev)*);
    if is_Eq ev then
      let e1,e2 = destr_Eq ev in
      let e = if side then e2 else e1 in
      F.fprintf fmt 
        "proc; rnd ((=) (%a));@   conseq (_ : _ ==> true); last by [].@ "
        Printer.pp_form (formula file [g.mod_name] None e);
      F.fprintf fmt "progress.@ ";
      F.fprintf fmt "apply Real.eq_le;apply %s." lemma
    else assert false;
    F.fprintf fmt "@]" in
  let lemma = add_pr_lemma file (mk_cmp pr cmp_le bound) (Some proof) in
  lemma, pr, cmp_le, bound

let extract_except file pos _l pft pft' = 
  let ju = pft.pt_ju in
  let ju' = pft'.pt_ju in
  let pr = extract_pr file mem ju in
  let pr' = extract_pr file mem ju' in
  let g = game file pft.pt_ju.ju_se.se_gdef in 
  let g' = game file pft'.pt_ju.ju_se.se_gdef in
  let vcs = vc_oracles file in
  let nvc = List.length vcs in
  let npos = pos + nvc in
  let side, adv =
    let comp = match g.mod_body with 
      | Mod_def cmp -> cmp 
      | _ -> assert false in
    let comp, f = 
      match List.rev comp with 
      | MCfun f :: r -> List.rev r, f
      | _ -> assert false in
   
    let side, x, ex =
      match List.nth ju.ju_se.se_gdef pos, List.nth ju'.ju_se.se_gdef pos with 
      | GSamp(x,(_ty,[])), GSamp(x',(_ty',[e])) -> 
        assert (Vsym.equal x x'); (* FIXME: check ty *)
        `LeftToRight, x, e
      | GSamp(x,(_ty,[e])), GSamp(x',(_ty',[])) ->
        assert (Vsym.equal x x');
        `RightToLeft, x, e
      | _, _ -> assert false in
    let hd,_,tl = Util.split_n npos (f_body f) in
    let a1 = 
      let res = ([], "_res") in
      let dres = res, mk_Fq in
      let ex = expression file ex in
      { f_name = "a1";
        f_def = Fbody {
        f_param = [];
        f_local = [dres];
        f_res   = Some dres;
        f_body  = List.rev_append hd [Iasgn([res],ex)] } } in
    let a2 = 
      let arg = ([], "_arg") in
      let darg = arg, mk_Fq in
      {
        f_name = "a2";
        f_def = Fbody {
        f_param = [darg];
        f_local = [];
        f_res   = None;
        f_body  = Iasgn([pvar [] x], Epv arg)::tl } } in
    let advname = top_name file ("SDadv") in 
    side, { mod_name = advname;
      mod_param = [];
      mod_body = Mod_def (comp @ [MCfun a1; MCfun a2]) } in
  add_game file `Local adv;
  let clone_info = {
    ci_local = true;
    ci_import = true;
    ci_from   = "SDField";
    ci_as     = top_name file "SDField_";
    ci_with   = [];
    ci_proof  = []; 
  } in
  add_local file (Cclone clone_info);
  let eps = f_rinv (Frofi f_Fq) in
  let bound = f_radd pr' (f_rinv (Frofi f_Fq)) in
  let pr1, pr2 = if side = `LeftToRight then pr, pr' else pr', pr in
  let g2 = if side = `LeftToRight then g' else g in

  let ev = formula file [adv.mod_name] None ju.ju_se.se_ev in 
  let mk_eqs g fv = 
    let mk_eq e = 
      f_eq (formula file [g] (Some "1") e) 
        (formula file [adv.mod_name] (Some "2") e) in
    match Se.elements fv with
    | [] -> f_true
    | e :: es -> List.fold_left (fun f e -> f_and f (mk_eq e)) (mk_eq e) es in
  let fv = e_vars ju.ju_se.se_ev in
  let nA = adv_name file in
  let eqvc = mk_eq_vcs g2 adv vcs in
  let proof fmt () = 
    F.fprintf fmt "intros &m.@ ";
      F.fprintf fmt 
      "cut -> : @[%a =@ Pr[SDF.SD1query.SD1(%s, S).main() @@ &m :@ %a]@].@ " 
      Printer.pp_form pr1 adv.mod_name Printer.pp_form ev;
    F.fprintf fmt 
      "  byequiv (_ : ={glob %s} ==> _);[ proc;inline *;sim | by [] | by [] ]. @ "
      nA;
    
    F.fprintf fmt 
      "cut -> : @[%a =@ Pr[SDF.SD1query.SD1(%s, SE).main() @@ &m :@ %a]@].@ " 
      Printer.pp_form pr2 adv.mod_name Printer.pp_form ev;
    F.fprintf fmt 
      "  byequiv (_ : ={glob %s} ==> _);[ proc;inline *;sim | by [] | by [] ]. @ "
      nA;
    F.fprintf fmt "  rnd; wp %i %i => /=.@ " npos (npos + 1);
    F.fprintf fmt "  conseq (_ : _ ==> ={glob %s} /\\ %a) => //;sim.@ " nA
      Printer.pp_form 
        (f_and eqvc (mk_eqs g2.mod_name 
                       (write_gcmds (Util.take pos ju.ju_se.se_gdef))));

    F.fprintf fmt "pose EV := fun (g:glob %s) (u:unit),@ " adv.mod_name;
    List.iter (fun e -> 
      let v = destr_V e in
      F.fprintf fmt "  let %a = g.`%s.%a in@ "
        Vsym.pp v adv.mod_name Vsym.pp v) (Se.elements fv);
    F.fprintf fmt "  @[%a@].@ "
      Printer.pp_form (formula file [] None ju.ju_se.se_ev);
    F.fprintf fmt "apply (%s.%s %s &m EV)." 
      clone_info.ci_as
      (if side = `LeftToRight then "SD1_conseq_add" else "SD1_conseq_add_E")
      adv.mod_name
  in
  
  let lemma = add_pr_lemma file (mk_cmp pr cmp_le bound) (Some proof) in
  lemma, pr, cmp_le, eps


(* Add test *)

let add_adv_add_test_bad file seoc auxname asym infob info gb = 
  let clone = {
    ci_local  = false;
    ci_import = false;
    ci_from   = auxname;
    ci_as     = auxname;
    ci_with   = 
      Osym.H.fold (fun o _oi w -> 
        CWop(q_oracle_i infob o, None, Ecnst (q_oracle file o)) :: w)
        infob.adv_g.oinfo [];
    ci_proof   = 
      Osym.H.fold (fun o _oi p -> 
        let ax = q_oracle_i infob o ^ "_pos" in
        let pr = Format.sprintf "apply %s_pos"  (q_oracle file o) in
        (ax, fun fmt () -> F.fprintf fmt "%s" pr)::p )
        infob.adv_g.oinfo [];
  } in
  add_top file (Cclone clone);
  (* Build the adversary for pftb *) 
  let gadv_test = 
    let nA,aT = adv_decl file in
    let nO,oT = "O", infob.adv_oty in
    let ni = ([],"__i__") in
    let nx = ([],"__x__") in
    let esave = mk_Tuple (List.map mk_V seoc.seoc_oargs) in
    let nc = vc_oracle [] seoc.seoc_osym in
    let odef = 
      Osym.H.fold (fun o oi l ->
        let name = "o" ^ Osym.to_string o in
        let def = 
          if Osym.equal o seoc.seoc_osym then
            let oinfo = oracle_info infob o in
            let res = "_res" in
            let vres = [],res in
            let eargs = List.map mk_V oinfo.oparams in
            let eargs = List.map (expression file) eargs in
            let et = Etuple eargs in
            Fbody {
              f_param = 
                List.map (fun v -> pvar [] v, v.Vsym.ty) oinfo.oparams;
              f_local = [vres,oinfo.ores];
              f_res = Some (vres, oinfo.ores);
              f_body = 
                [Iif(e_lt (e_pv nc) (Ecnst (q_oracle file o)),
                     [Iif(e_eq (e_pv nc) (e_pv ni), [Iasgn([nx], et)], []);
                      Iasgn([nc], e_incr (e_pv nc))], 
                     []);
                 Icall([vres], (mod_name nO [], name),
                       eargs)] }
          else if Osym.H.mem infob.adv_g.oinfo o then
            Falias (mod_name nO [], name)
          else 
            let res = "_res" in
            let vres = [],res in
            Fbody {
              f_param = 
                List.map (fun v -> pvar [] v, v.Vsym.ty) oi.oparams;
              f_local = [vres,oi.ores];
              f_res = Some (vres, oi.ores);
              f_body = [
                Iasgn([vres], expression file (init_res_expr oi.ores)) ] }
        in
        MCfun {f_name = name; f_def = def}::l) info.adv_g.oinfo [] in
    let modo = 
      { mod_name = "O'";
        mod_param = [];
        mod_body  = Mod_def (List.rev odef); } in
    let moda = {
      mod_name = "A";
      mod_param = [];
      mod_body  = Mod_alias (mod_name nA [mod_name "O'" []]) } in
    let aprocs = 
      List.rev (
        Asym.H.fold (fun an _ l ->
          let aname = "a"^Asym.to_string an in 
          let aname' = "a" ^ Asym.to_string seoc.seoc_asym in
          let body = 
            if Asym.equal an asym then
              let varg = ([],"arg") in
              let vaux = ([],"aux") in
              let q  = Ecnst (q_oracle file seoc.seoc_osym) in 
              Fbody {
                f_param = [varg, asym.Asym.dom];
                f_local = [vaux, seoc.seoc_asym.Asym.codom];
                f_res   = Some (nx,esave.e_ty);
                f_body  = 
                  [ Irnd_int ([ni], e_int0, e_sub q e_int1);
                    Iasgn([nc], e_int0);
                    Icall([vaux],(mod_name "A" [], aname'), [e_pv varg]) ]
              }
            else Falias (mod_name "A" [], aname) in
          MCfun{f_name = aname; f_def = body} :: l) infob.adv_g.ainfo [])
            
    in
    
    { mod_name  = top_name file ("Adv_"^auxname);
      mod_param = [(nA,aT); nO,Format.sprintf "%s.%s" auxname oT];
      mod_body  = Mod_def 
        (MCvar(ni,mk_Int)::
           MCvar(nx,esave.e_ty)::
           MCvar(nc,mk_Int)::
           MCmod modo ::
           MCmod moda ::
           aprocs)} in
  add_game file `Top gadv_test;
    (* extend the restriction *)
  let restr = List.filter (fun s -> gb.mod_name <> s) infob.adv_restr in
  let restr = List.map (fun s -> Format.sprintf "%s.%s" auxname s) restr in
  info.adv_restr <- restr @ info.adv_restr;
  gadv_test

let add_adv_orcl_test file g evars etuple ctests t1 t2 seoc = 
  let tOrclTest = top_name file "OrclTest" in
  let doproj e = pvar [] (destr_V e) in
  let et1 = 
    expression file (mk_Land (List.rev_append ctests [t1])) in
  let et2 = 
    expression file (mk_Land (List.rev_append ctests [t1;t2])) in
  let cloneOT = {
    ci_local  = true;
    ci_import = false;
    ci_from   = "OrclTest";
    ci_as     = tOrclTest;
    ci_with   = 
      [CWtype("U", etuple.e_ty);
       CWop ("t1", Some (([],"x"),etuple.e_ty, List.map doproj evars),
             et1);
       CWop ("t2", Some (([],"x"),etuple.e_ty, List.map doproj evars),
             et2);
       CWop ("q", None, Ecnst (q_oracle file seoc.seoc_osym))
      ];
    ci_proof   = [];
  } in
  add_local file (Cclone cloneOT);
 
  let gcomp = 
    match g.mod_body with Mod_def c -> c | _ -> assert false in

  let cv = vc_oracle [] seoc.seoc_osym in
  let gvar = 
    List.filter (function MCvar (x,_) -> x <> cv | _ -> false) gcomp in
  let find_mod name = 
    List.find (function MCmod m -> m.mod_name = name | _ -> false) gcomp in
  let o = 
    match find_mod "O" with
    | MCmod ({mod_body = Mod_def ocomp} as mo) ->
      let oname = "o" ^ Osym.to_string seoc.seoc_osym in 
      let ocomp = 
        List.map 
          (function MCfun f when f.f_name = oname -> 
            let body = 
              match f.f_def with Fbody body -> body | _ -> assert false in
            let i,s =
              match body.f_body with
              | [i; Iif(_, _::s,[])] -> i,s
              | _ -> assert false in
            let rec aux n s = 
              if n = 0 then s
              else match s with
              | [Iif(_,s,[])] -> aux (n-1) s 
              | _ -> assert false in
            let s = aux (List.length ctests + 1) s in
            let vt = [],"___t___" in
            let it = 
              Icall([vt], (mod_name "OT" [],"o"), [expression file etuple]) in
            let iif = Iif (e_pv vt, s, []) in
            let body = { body with 
              f_local = (vt,mk_Bool)::body.f_local;
              f_body = [i;it;iif] } in
            MCfun {f with f_def = Fbody body }
          | c -> c) ocomp in
      
      MCmod {mo with mod_body = Mod_def ocomp}
    | _ -> assert false in
  let nA = adv_name file in
  let a = find_mod nA in
  let a1,a2 = 
    let main = 
      List.find (function MCfun f -> f.f_name = "main" | _ -> false) gcomp in
    let body = 
      match main with 
      | MCfun {f_def = Fbody body} -> body 
      | _ -> assert false in
    let c1, c2 = 
      let fadv =  (mod_name nA [],"a" ^ Asym.to_string seoc.seoc_asym) in
      let test i = 
        match i with
        | Icall(_,f,_) -> f = fadv
        | _ -> false in
      let rec aux r c = 
        match c with
        | [] -> assert false
        | i :: c ->
          if test i then List.rev_append r [i], c
          else aux (i::r) c in
      aux [] body.f_body in
    let c1 = 
      let vc = vc_oracle [] seoc.seoc_osym in
      List.filter (function Iasgn([v], _) -> v <> vc | _ -> true) c1 in
    let body1 = {f_param = []; f_local = []; f_res   = None; f_body  = c1 } in
    let body2 = {f_param = []; f_local = []; f_res   = None; f_body  = c2 } in
    let a1 = MCfun {f_name = "a1"; f_def = Fbody body1 } in
    let a2 = MCfun {f_name = "a2"; f_def = Fbody body2 } in
    a1, a2 in
  let aotname = top_name file "AdvOT" in
  let aotdef = {
    mod_name  = aotname;
    mod_param = ["OT", tOrclTest^".OT"];
    mod_body  = Mod_def (gvar @ [o;a;a1;a2]);
  } in
  add_game file `Local aotdef;
  tOrclTest, aotdef, et2  


let proof_OrclTestM file osym ju gadv tOT tests =
  let g = get_game file ju.ju_se.se_gdef in
  let open_pp, close_pp = init_same_ev file None "[]" in
  let add_asgn v info =
    let e1 = formula file [g.mod_name] (Some "1")  (Expr.mk_V v) in
    let e2 = formula file [gadv.mod_name] (Some "2") (Expr.mk_V v) in
    { info with
      pos1 = info.pos1 + 1;
      pos2 = info.pos2 + 1;
      tacs = add_wp info.pos1 info.pos2 info.tacs;
      invs = f_and info.invs (f_eq e1 e2) } in
  let add_rnd v info =
    let e1 = formula file [g.mod_name] (Some "1")  (Expr.mk_V v) in
    let e2 = formula file [gadv.mod_name] (Some "2") (Expr.mk_V v) in
    { info with
      pos1 = info.pos1 + 1;
      pos2 = info.pos2 + 1;
      tacs = add_rnd info.tacs;
      invs = f_and info.invs (f_eq e1 e2) } in
  let add_call vs odefs info =
    let prove_orcl o =
      let (o,p,_,_,_) = o in
      if Osym.equal o osym then 
        let local = List.fold_left (fun s v -> Vsym.S.add v s) Vsym.S.empty p in
(*        let tests = List.map destr_guard juoc.juoc_cleft in
        let tests = List.rev_append tests [test] in        *)
        let inv = 
          f_and (init_inv_oracle p p info.invs)
            (f_eq (Fv (([],"___t___"), Some "2"))
               (formula file [g.mod_name] ~local (Some "1") (mk_Land tests))) in
        let rec t_end n =
          if n = 0 then 
            [Tac (Tstring 
                    "rcondt{2} 1;[by move=> &m0; skip;progress;smt | by sim]")]
          else
            [Tac (Tstring "if{1}");
             TSub [t_end (n-1)];
             Tac (Tstring
                    "rcondf{2} 1;[by move=> &m0; skip;progress;smt | sim]")] in
        let sub = 
          (Tac (TSeqSub (Seq(1,4,inv), [Tstring "by auto"; t_id]))) ::
            t_end (List.length tests) in
        [Tac (Tstring "proc;inline *; sp 1 3;if;first by done");
         TSub [sub];
         Tac (Tstring "rcondf{2} 2;[by move=> &m0;wp;skip;progress | by sim]")]
      else [Tac (Tstring "by sim")] in
    let mk_eq v = 
      let e1 = formula file [g.mod_name] (Some "1") (Expr.mk_V v) in
      let e2 = formula file [gadv.mod_name] (Some "2") (Expr.mk_V v) in 
      f_eq e1 e2 in
    let eqs = List.map mk_eq vs in
    let pr_orcls = List.map prove_orcl odefs in
    { loc1 = info.loc1;
      loc2 = info.loc2;
      pos1 = info.pos1 + 1;
      pos2 = info.pos2 + 1;
      tacs = Tac (Call info.invs) :: TSub pr_orcls :: info.tacs;
      invs = List.fold_left f_and info.invs eqs } in
    
  let rec gaux lc info =
    match lc with
    | [] -> info
    | GLet(v,_)::lc -> gaux lc (add_asgn v info)
    | GSamp(v,_)::lc -> gaux lc (add_rnd v info)
    | GCall(vs,_,_,odef)::lc -> gaux lc (add_call vs odef info) in
  
  let vcs = vc_oracles file in
  let nvc = List.length vcs in
  let vco = vc_oracle [] osym in
  let eqvc =
    let mk_eq v = f_eq (f_v g v "1") (f_v gadv v "2") in
    List.fold_left (fun inv v ->
      let eq = 
        if snd v = snd vco then
          f_eq (f_v g v "1") (Fv (([tOT;"C"],"c"), Some "2")) 
        else mk_eq v in
      f_and inv eq) f_true vcs in

  let info = 
    { loc1 = Vsym.S.empty; loc2 = Vsym.S.empty;
      pos1 = nvc; pos2 = nvc;
      tacs = [Tac Auto]; invs = eqvc } in
  let info = gaux ju.ju_se.se_gdef info in

  fun fmt () ->
    open_pp fmt ();
    F.fprintf fmt "(* OrclTestM *)@ ";
    F.fprintf fmt "inline *.@ ";
    pp_cmds fmt info.tacs;
    close_pp fmt ()
  
let proof_OrclB file infob tOT advOT mb aAUX jucb seoc etuple et2 = 

  let open_pp, close_pp = init_same_ev file None "[]" in
  let cs = 
    match List.rev jucb.ju_se.se_gdef with
    | _::cs -> List.rev cs 
    | [] -> assert false in
  let write = write_gcmds cs in
  let eqw = mk_eq_exprs_p file advOT mb write in
  let vcs = vc_oracles_i infob in
  let nvc = List.length vcs in
  let vco = vc_oracle [mb] seoc.seoc_osym in
  let eqvcw0 =
    let mk_eq v = f_eq (Fv(([advOT],v),Some "1")) (Fv(([mb],v),Some "2")) in
    List.fold_left (fun inv (_,v) ->
        if v = snd vco then inv
        else f_and inv (mk_eq v)) eqw vcs in 
  let eqc = f_eq (Fv(([tOT;"C"],"c"),Some "1")) (Fv(vco,Some "2")) in
  let eqvcw = f_and eqvcw0 eqc in
  let gu = Fv(([tOT;"B"],"gu"),Some "1") in
  let find_args =
    let args = List.mapi (fun i v -> (i+1,v)) seoc.seoc_oargs in
    List.fold_left (fun m (i,v) ->
      Vsym.M.add v (Fproj(i, Fv(([aAUX],"__x__"), Some "2"))) m)
      Vsym.M.empty args in
  let inv = 
    let ftuple = 
      let es = destr_Tuple_nofail etuple in
      let fs = 
        List.map (fun e ->
          let v = destr_V e in
          try Vsym.M.find v find_args 
          with Not_found ->
            formula file [mb] (Some "2") e) es in
      Ftuple fs in
    f_imp (f_not (f_eq gu (Fcnst "None")))
      (f_eq gu (Fapp (Ostr "Some", [ftuple]))) in
  let eqi = 
    let c = snd (vc_oracle [] seoc.seoc_osym) in
    f_and 
      (f_eq (Fv(([tOT;"B"],"i"), Some "1")) (Fv(([aAUX],"__i__"),Some "2")))
      (f_eq (Fv(([mb],c), Some "2")) (Fv(([aAUX],c),Some "2"))) in
  let nA = adv_name file in
  let len = List.length cs in
  let len2 = len + nvc - 1 in
  let len1 = len + List.length (vc_oracles file) - 1 in
  let invcall = f_and eqi (f_and inv eqvcw) in
  let invargs = 
    let add_eq f v = 
      f_and f (f_eq (Fv(pvar [] v, Some "1")) (Fv(pvar [] v, Some "2"))) in
    List.fold_left add_eq invcall seoc.seoc_oargs in
  let pp_eqt fmt () =
    let xs = List.map destr_V (destr_Tuple_nofail etuple) in
    let pp_v fmt x = 
      try 
        ignore (Vsym.M.find x find_args);
        Vsym.pp fmt x
      with Not_found ->
        F.fprintf fmt "%s.%a" advOT Vsym.pp x in
    F.fprintf fmt "@[<hov 2>(r{1} =@ let (@[%a@]) =@ (@[%a@]){1} in@ %a)@]"
      (pp_list ",@ " Vsym.pp) xs 
      (pp_list ",@ " pp_v) xs 
      Printer.pp_exp et2 
      
  in 
  
  let pr_oracle fmt o = 
    if Osym.equal o seoc.seoc_osym then 
      let nargs = List.length seoc.seoc_oargs in
      F.fprintf fmt "proc;inline *;if{2}.@ ";
      F.fprintf fmt "  rcondt{1} 4; first by auto.@ ";
      F.fprintf fmt "  rcondt{2} %i; first by auto.@ " (nargs + 4);
      F.fprintf fmt "  swap{1} 1 8.@ "; 
      F.fprintf fmt "  swap{2} %i -%i.@ " (nargs + 4) (nargs + 1);
      F.fprintf fmt "  seq 8 3 : (@[%a /\\@ %a@]).@ "
        pp_eqt () Printer.pp_form invargs;         
      F.fprintf fmt "    by auto;progress [-split];smt.@ ";
      F.fprintf fmt "  sp 2 %i.@ "(nargs + 1);
      for _i = 1 to List.length seoc.seoc_cleft + 2 do
        F.fprintf fmt 
          "  if{2};last by rcondf{1} 1;auto;progress [-split];smt.@ ";
      done;
      F.fprintf fmt "  rcondt{1} 1;first by auto;progress [-split];smt.@ ";
      F.fprintf fmt "  by conseq * (_: _ ==> ={_res});[by done | sim].@ ";
      F.fprintf fmt "rcondf{1} 4;[ by auto | rcondf{1} 5;first by auto ].@ ";
      F.fprintf fmt "by rcondf{2} %i; auto."  (nargs + 2)
    else 
      F.fprintf fmt "conseq* (_: _ ==> ={res});[by done | by sym]." in
  fun fmt () ->
    open_pp fmt ();
    F.fprintf fmt "(* OrclTest.B *)@ ";
    F.fprintf fmt "inline *;auto => /=.@ ";
    F.fprintf fmt "conseq (@[<hov>_ : _ ==> %a@]).@ "
      Printer.pp_form (f_and inv eqw);
    F.fprintf fmt "  by move=> &m1 &m2 [Hi He] [Hn ]; move: He; @ ";
    F.fprintf fmt "   rewrite (Hi Hn) oget_some;progress [-split];smt.@ ";
    F.fprintf fmt "call (_: @[<hov>%a@]).@ "
      Printer.pp_form invcall;
    let ol  = List.map (fun (o,_,_,_,_) -> o) seoc.seoc_oleft in
    let or_ = List.map (fun (o,_,_,_,_) -> o) seoc.seoc_oright in
    F.fprintf fmt "  @[<v>%a@]@ "
      (pp_list "@ " pr_oracle) (List.rev_append ol (seoc.seoc_osym :: or_));
    F.fprintf fmt "swap{1} [1..3] %i;swap{2} 1 %i.@ " len1 len2;
    F.fprintf fmt "seq %i %i: (@[={glob %s} /\\ %a@]);[by sim | by auto]."
      len1 len2 nA Printer.pp_form eqvcw0;
    close_pp fmt ()

(*call (_: 
           OrclTest0.B.i{1} =  Adv_AUXILIARY0.__i__{2} /\
           M4.cDec2{2} = Adv_AUXILIARY0.cDec2{2} /\
          (OrclTest0.B.gu{1} <> None =>
          ( OrclTest0.B.gu{1} = Some (M4.w, M4.x2, M4.x1, M4.y2, M4.y1, M4.z2, M4.u, 
             Adv_AUXILIARY0.__x__.`1,   Adv_AUXILIARY0.__x__.`2, Adv_AUXILIARY0.__x__.`3, 
             Adv_AUXILIARY0.__x__.`4, M4.v){2})) /\
          OrclTest0.C.c{1} = M4.cDec2{2} /\
          AdvOT.cDec1{1} = M4.cDec1{2} /\
          AdvOT.w{1} = M4.w{2} /\
          AdvOT.u{1} = M4.u{2} /\
          AdvOT.v{1} = M4.v{2} /\
          AdvOT.y2{1} = M4.y2{2} /\
          AdvOT.x1{1} = M4.x1{2} /\
          AdvOT.y1{1} = M4.y1{2} /\
          AdvOT.z1{1} = M4.z1{2} /\
          AdvOT.m0{1} = M4.m0{2} /\
          AdvOT.m1{1} = M4.m1{2} /\
          AdvOT.b{1} = M4.b{2} /\
          AdvOT.x2{1} = M4.x2{2} /\
          AdvOT.z2{1} = M4.z2{2}). *)

  
let default_proof file mem s pft = 
  F.eprintf "WARNING rule %s not extracted@." s;
  let pr = extract_pr ~local:`Top file mem pft.pt_ju in
  let lemma = add_pr_lemma file (mk_cmp pr cmp_eq pr) 
    (Some (fun fmt () -> 
      F.fprintf fmt "(* WARNING rule %s not extracted*)@ " s;
      F.fprintf fmt "trivial.")) in
  lemma, pr, cmp_eq, pr 

let pp_cintros fmt hs =
  match hs with
  | [] -> assert false
  | [h] -> F.fprintf fmt "%s" h
  | hs -> 
    let rec aux fmt hs =
      match hs with
      | [] -> ()
      | [h] ->  F.fprintf fmt "%s" h
      | h::hs -> F.fprintf fmt "[%s %a]" h aux hs in
    F.fprintf fmt "@[<hov>%a@]" aux hs 

let rec extract_proof file pft = 
  match pft.pt_rule with
  | Rtrans    -> assert false
  | Rdist_sym -> assert false
  | Rdist_eq -> assert false
  | Rhybrid  -> assert false
  | Rswap_main _ -> assert false
  | Rconv -> 
    extract_conv file pft [] pft

  | Rctxt_ev (i,_) ->
    let pft' = List.hd pft.pt_children in
    let ev = pft.pt_ju.ju_se.se_ev in
    let evs = destr_Land_nofail ev in
    let hs = List.mapi (fun i _ -> Format.sprintf "H%i" i) evs in
    let proof _file fmt () = 
     
      F.fprintf fmt "move=> &m; rewrite Pr [mu_sub]; last by done.@ ";
      F.fprintf fmt "by intros &hr %a;rewrite H%i //;smt." pp_cintros hs i in
    extract_proof_sb1_le "Ctxt_ev" file pft pft' proof

  | Rremove_ev _ ->
    let pft' = List.hd  pft.pt_children in
    extract_proof_sb1_le "Remove_ev" file pft pft' 
      (fun _file fmt () -> F.fprintf fmt "rewrite Pr [mu_sub] => //.")

  | Rmerge_ev _ -> 
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "Merge_ev" file pft pft' (pr_admit "merge_ev")

  | Rrnd (pos,_,inv1,inv2) ->
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "Rnd" file pft pft' 
      (pr_random (pos,inv1,inv2) pft.pt_ju pft'.pt_ju)

  | Rrnd_orcl (pos, inv1, inv2) ->
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "rnd_orcl" file pft pft' 
      (pr_random_orcl (pos,inv1,inv2) pft.pt_ju pft'.pt_ju)

  | Rswap _ ->
    let sw1, pft' = skip_swap pft in
    begin match pft'.pt_rule with
    | Rconv -> extract_conv file pft sw1 pft'
    | _ ->
      (* FIXME *)
      extract_proof_sb1 "Swap" file pft pft' (pr_swap sw1 pft.pt_ju pft'.pt_ju)
    end
  | Rswap_orcl _ ->
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "Swap_oracle" file pft pft' (pr_admit "swap oracle")

  | Rrnd_indep (side, pos) ->
    extract_rnd_indep file side pos pft.pt_ju 
    
  | Rassm_dec (_ranges,_dir,_subst,_assum) ->
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "Dec_comp" file pft pft' (pr_admit "Decisional assumption")
    
    (*
    let pft' = List.hd pft.pt_children in
    let (lemma1, pr',cmp,bound) = extract_proof file pft' in
    let ainfo = 
      try Ht.find file.assump_dec assum.Ass.ad_name 
      with Not_found -> assert false in
    let lemma2, pr, abs = extract_assum file dir subst ainfo pft pft' in
    let proof fmt () = 
      F.fprintf fmt "@[<v>intros &m.@ ";
      F.fprintf fmt "@[apply (real_le_trans@ %a@ %a@ %a).@]@ "
        (Printer.pp_form_lvl Printer.min_lvl) pr 
        (Printer.pp_form_lvl Printer.min_lvl) (f_radd abs pr') 
        (Printer.pp_form_lvl Printer.min_lvl) (f_radd abs bound);
      F.fprintf fmt "apply (%s &m).@ " lemma2;
      F.fprintf fmt "apply Real.addleM; first by [].@ ";
      F.fprintf fmt "by %s (%s &m).@]"
        (if cmp = cmp_eq then "rewrite" else "apply") lemma1 in
    let bound = f_radd abs bound in
    let lemma3 = 
      add_pr_lemma file (mk_cmp pr cmp_le bound) (Some proof) in
    lemma3, pr, cmp_le, bound 
    *)

  | Rassm_comp (_ranges,_subst,_assum) ->
    default_proof file mem "admit" pft
    (*
    let ainfo = 
      try Ht.find file.assump_comp assum.Ass.ac_name 
      with Not_found -> assert false in
    extract_assum_comp file subst ainfo ranges pft
    *)

  | Rexc (pos,l)   -> 
    let pft' = List.hd pft.pt_children in
    let (lemma1, pr', cmp, bound) = extract_proof file pft' in
    (* pr' cmp bound *)
    let (lemma2, pr, _, eps) = extract_except file pos l pft pft' in
    (* pr <= pr' + eps *)
    let bound = f_radd bound eps in
    let proof fmt () = 
      F.fprintf fmt "@[<v>intros &m.@ ";
      F.fprintf fmt "@[apply (real_le_trans@ _@ %a@ _).@]@ "
        (Printer.pp_form_lvl Printer.min_lvl) (f_radd pr' eps);
      F.fprintf fmt "apply (%s &m).@ " lemma2;
      F.fprintf fmt "apply Real.addleM; last by [].@ ";
      F.fprintf fmt "by %s (%s &m).@]"
        (if cmp = cmp_eq then "rewrite" else "apply") lemma1 in
    let lemma3 = 
      add_pr_lemma file (mk_cmp pr cmp_le bound) (Some proof) in
    lemma3, pr, cmp_le, bound 

  | Radd_test (opos, tnew, asym, _fvs) -> 
    
    (* Perform the generic proof for bad event *)
    let pftb = List.hd pft.pt_children in 
    let auxname = init_section file "AUXILIARY" pftb in
    let lemmab, prb, cmpb, boundb = extract_proof file pftb in
    let conclusion = top_name file "conclusion" in
    let gb = get_game file pftb.pt_ju.ju_se.se_gdef in
    let body = forall_mem (mk_cmp prb cmpb boundb) in
    let proof fmt () = 
      F.fprintf fmt "apply %s." lemmab in
    add_local file (Clemma(false, conclusion,body, Some proof));
    let infob = adv_info file in
    let secb = get_section file in
(*    begin
      match secb.section_loc with
      | Some ({loca_decl = Clemma(b,l,f,_)::_} as ls) -> 
        ls.loca_decl <- [Clemma(b,l,f,Some 
          (fun fmt () -> F.fprintf fmt "admit."))]
      | _ -> assert false
    end; *)
        
    end_section file;
    (* End theory bad event *)
    let info = adv_info file in
    let t1, seoc = get_se_octxt pft.pt_ju.ju_se opos in 
    let t1 = destr_guard t1 in
    let t2 = tnew in
    let ctests = List.map destr_guard seoc.seoc_cleft in
    let allt = mk_Land (t1::t2::ctests) in
    let evars = Se.elements (ExprUtils.e_vars allt) in
    let etuple = Expr.mk_Tuple evars in
    let _tytuple = etuple.e_ty in

    (* Clone the theory for bad event + build the adversary for bad *)
    let aAT = 
      add_adv_add_test_bad file seoc auxname asym infob info gb in
   
    (* Build sub proof with the new test *)
    let pft' = List.hd (List.tl pft.pt_children) in
    let (lemma', pr',cmp',bound') = extract_proof file pft' in 
   
    (* Clone AddTest + build the corresponding adversary *)
    let g = game file pft.pt_ju.ju_se.se_gdef in 
    let tOT, advOT, et2 = 
      add_adv_orcl_test file g evars etuple ctests t1 t2 seoc in
   
    (* localy clone the section for bad *)
    let auxname_Loc = auxname^"_Loc" in
    let lclone = {
      ci_local  = true;
      ci_import = true;
      ci_from   = auxname^".Local";
      ci_as     = auxname_Loc;
      ci_with   = [];
      ci_proof  = [];
    } in
    add_local file (Cclone lclone); 
    (* Perform all the lemma *)
    let pr = extract_pr file mem pft.pt_ju in
    let ev = formula file [advOT.mod_name] None pft.pt_ju.ju_se.se_ev in
    let mOT s = Format.sprintf "%s.%s" tOT s in
    let tOTM = mOT "M" in
    let mOt1 = mod_name (mOT "Ot1") []  in
    let mOt2 = mod_name (mOT "Ot2") []  in
    let mA   = mod_name advOT.mod_name [] in
    let m1   = mod_name tOTM [mOt1; mA] in
    let m2   = mod_name tOTM [mOt2; mA] in
    let praOT1 = Fpr((m1,"main"), mem, [], ev) in
    let praOT2 = Fpr((m2,"main"), mem, [], ev) in
    let tests = List.map destr_guard seoc.seoc_cleft in
    let lemma1 = 
      let tests = List.rev_append tests [t1] in
      let proof = 
        proof_OrclTestM file seoc.seoc_osym pft.pt_ju advOT tOT tests in
      add_pr_lemma file (mk_cmp pr cmp_eq praOT1) (Some proof) in
    let lemma2 = 
      let tests = List.rev_append tests [t1;t2] in
      let proof = 
        proof_OrclTestM file seoc.seoc_osym pft'.pt_ju advOT tOT tests in
      add_pr_lemma file (mk_cmp pr' cmp_eq praOT2) (Some proof) in
    (* build the subtitution *)
    let ms = 
      let ms = 
        List.fold_left (fun ms s ->
          Mstring.add s {mn = Format.sprintf "%s.%s" auxname s;ma = []} ms) 
          Mstring.empty secb.tosubst in
      Mstring.add infob.adv_name 
        {mn = aAT.mod_name ;ma = [adv_mod file]} ms in
    (* FIXME add the ms in tosubst of the current section *)
    let mc = 
      Osym.H.fold (fun o _oi mc -> 
        Mstring.add (q_oracle_i infob o) (Fcnst (q_oracle file o)) mc)
        infob.adv_g.oinfo Mstring.empty in
 
    let prMb = 
      let mb = mod_name (mOT "B") [mA] in
      Fpr((mb,"main"), mem, [], Fv(([],"res"),None)) in
    let prb = subst_f ms mc prb in
    let lemma3 = 
      let proof = 
        proof_OrclB file infob tOT 
          advOT.mod_name gb.mod_name aAT.mod_name
          pftb.pt_ju seoc etuple et2 in
      add_pr_lemma file (mk_cmp prMb cmp_le prb) (Some proof) in
    let boundb = subst_f ms mc boundb in

    let qo = q_oracle_i info seoc.seoc_osym in
    let bound = f_radd bound' (f_rmul (Frofi (Fcnst qo)) boundb) in
    let nA = adv_name file in
    let proof fmt () = 
      let sadvOT = advOT.mod_name in
      let pp_E fmt () = 
        let ev = pft.pt_ju.ju_se.se_ev in
        let fv = Se.elements (ExprUtils.e_vars ev) in
        let f = formula file [] None ev in
        let pp_let fmt v = 
          let v = Vsym.to_string (destr_V v) in
          F.fprintf fmt "let %s = gl.`%s.%s in@ " v sadvOT v in
        F.fprintf fmt "(@[<v>fun (gl:glob %s),@   @[<v>%a@[<hov>%a@]@]@])"
          sadvOT (pp_list "" pp_let) fv Printer.pp_form f in
      F.fprintf fmt "move=> &m;rewrite (%s &m).@ " lemma1;
      F.fprintf fmt "cut := %s.add_test %s &m@ " tOT sadvOT; 
      F.fprintf fmt "  %a.@ " pp_E ();
      F.fprintf fmt 
        "beta iota zeta modpath=> H; apply (real_le_trans _ _ _ H).@ ";
      F.fprintf fmt "apply Real.addleM.@ ";
      F.fprintf fmt "  by rewrite -(%s &m);%s (%s &m).@ "
        lemma2 (if cmp' = cmp_eq then "rewrite" else "apply") lemma';
      F.fprintf fmt "apply mulleM;last by move=> /=;apply %s_pos.@ " qo;
      F.fprintf fmt "(split;first by smt)=> _.@ ";
      F.fprintf fmt "cut {H}H := %s &m;apply (real_le_trans _ _ _ H).@ " lemma3;
      F.fprintf fmt "apply (%s.%s (<:Adv_%s(%s)) &m)." 
        auxname_Loc conclusion auxname nA
    in
    let concl = 
      add_pr_lemma file (mk_cmp pr cmp_le bound) (Some proof) in
    concl, pr, cmp_le, bound 


  | Rexc_orcl _ -> 
    default_proof file mem "exc_orl" pft

  | Rrw_orcl (op,dir)  -> 
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 "Rw_orcl" file pft pft' 
      (pr_rw_orcl (op,dir) pft.pt_ju pft'.pt_ju)


  | Rbad     _  -> default_proof file mem "bad" pft
  | Radmit _    -> default_proof file mem "admit" pft

  | Rfalse_ev   -> 
    let ju = pft.pt_ju in
    let pr = extract_pr file mem ju in
    let bound = f_r0 in
    let proof fmt () = 
      F.fprintf fmt "@[<v>by intros &m; rewrite Pr [mu_false].@]" in
    let lemma = add_pr_lemma file (mk_cmp pr cmp_eq bound) (Some proof) in
    lemma, pr, cmp_eq, bound

  | Rcase_ev (flip, e) -> 
    let pft1 = List.nth pft.pt_children (if flip then 1 else 0) in
    let pft2 = List.nth pft.pt_children (if flip then 0 else 1) in
    let (lemma1, _pr1, cmp1, bound1) = extract_proof file pft1 in
    let (lemma2, _pr2, cmp2, bound2) = extract_proof file pft2 in
    let pr = extract_pr file mem pft.pt_ju in
    let cmp = cmp1 && cmp2 in
    let bound = f_radd bound1 bound2 in
    let g = find_game file pft.pt_ju.ju_se.se_gdef in
    let ev = formula file [g.mod_name] None e in
    let proof fmt () =
      F.fprintf fmt "(* Case event *)@ ";
      F.fprintf fmt "move=> &m.@ ";
      F.fprintf fmt "rewrite Pr [mu_split (%a)].@ " Printer.pp_form ev;
      if cmp = cmp_le then 
        let aux fmt (cmp,lemma) =
          if cmp = cmp_eq then
            F.fprintf fmt 
              "by cut H1 := %s &m; cut H := Real.eq_le _ H1;" lemma
          else
            F.fprintf fmt "by cut H:= %s &m;" lemma;
          F.fprintf fmt 
            "apply (real_le_trans _ _ _ _ H);rewrite Pr [mu_sub]." in
        F.fprintf fmt "apply Real.addleM.@ ";
        F.fprintf fmt "  %a@ " aux (cmp1,lemma1);
        F.fprintf fmt "%a" aux (cmp2,lemma2)
      else 
        F.fprintf fmt "by rewrite (%s &m) (%s &m)." lemma1 lemma2 in

    let lemma3 = add_pr_lemma file (mk_cmp pr cmp bound) (Some proof) in
    lemma3, pr, cmp, bound

  | Rsplit_ev _i -> 
    let pft' = List.hd pft.pt_children in
    let proof _file fmt () = 
      F.fprintf fmt "(* split_ev *)@ ";
      F.fprintf fmt "by move=> &m;rewrite Pr [mu_eq]." in
    extract_proof_sb1 "split_ev" file pft pft' proof

  | Rrw_ev (i, dir) -> 
    let pft' = List.hd pft.pt_children in
    let proof _file fmt () = 
      let ev = pft.pt_ju.ju_se.se_ev in
      let evs = destr_Land_nofail ev in
      let his = List.mapi (fun i _ -> Format.sprintf "H%i" i) evs in
      let hi = Format.sprintf "H%i" i in
      let his' = List.filter (fun s -> s <> hi) his in
      F.fprintf fmt "rewrite Pr [mu_sub];last by done.@ ";
      F.fprintf fmt "by move=> &m %a;move: %a;rewrite %sH%i." 
        pp_cintros his 
        (pp_list " " (fun fmt -> F.fprintf fmt "%s")) his'
        (if dir = LeftToRight then "-" else "")
        i in
                         
    extract_proof_sb1_le "Rw_ev" file pft pft' proof

    
 
    

and extract_conv file pft sw1 pft1 =
  let pft2 = skip_conv pft1 in
  let sw2, pft' = skip_swap pft2 in 
  extract_proof_sb1 "Conv" file pft pft' 
    (pr_conv sw1 pft.pt_ju pft1.pt_ju pft2.pt_ju pft'.pt_ju sw2)

and extract_proof_sb1 msg file pft pft' proof = 
  let (lemma1, pr',cmp,bound) = extract_proof file pft' in
  let pr = extract_pr file mem pft.pt_ju in
  let proof = proof file in
  let lemma2 = 
    add_pr_lemma file (mk_cmp pr cmp_eq pr') 
      (Some proof) in
  let lemma3 = 
    add_pr_lemma file (mk_cmp pr cmp bound) 
      (Some (fun fmt () -> 
        F.fprintf fmt "(* %s *)@ " msg;
        pr_intr_rw1_app lemma2 lemma1 fmt ())) in
  lemma3, pr, cmp, bound

and extract_proof_sb1_le msg file pft pft' proof = 
  let (lemma1, pr',cmp,bound) = extract_proof file pft' in
  let pr = extract_pr file mem pft.pt_ju in
  let proof = proof file in
  let lemma2 = 
    add_pr_lemma file (mk_cmp pr cmp_le pr') 
      (Some proof) in
  let proof fmt () =
    F.fprintf fmt "(* %s *)@ " msg;
    F.fprintf fmt "intros &m; cut H1 := %s &m.@ " lemma2;
    F.fprintf fmt "apply (real_le_trans _ _ _ H1).@ ";
    F.fprintf fmt "by %s (%s &m)." 
      (if cmp = cmp_eq then "rewrite" else "apply") lemma1 in
  let lemma3 = 
    add_pr_lemma file (mk_cmp pr cmp_le bound) 
      (Some proof) in
  lemma3, pr, cmp_le, bound
  

let extract_file ts = 
  let pt = get_proof_tree ts in
  let pft = Rules.simplify_proof_tree pt in
  let file = init_file ts in
  let name = top_name file "conclusion" in
  ignore (init_section file "MAIN" pft);
  let lemma, pr, cmp, bound = extract_proof file pft in
  let body = forall_mem (mk_cmp pr cmp bound) in
  let proof fmt () = 
    F.fprintf fmt "apply %s." lemma in    
  add_local file (Clemma(false, name,body, Some proof));
  end_section file;
  file

let extract ts filename = 
  let file = extract_file ts in
  let out = open_out filename in
  let fmt = F.formatter_of_out_channel out in
  Printer.pp_file fmt file; 
  close_out out






















