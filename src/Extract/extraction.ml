open Util
open Type
open Expr 
open Game 
open Assumption
open TheoryState 
open CoreRules
open File
open Printer
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
  | V v -> Epv (pvar [] v)
  | H(h,e) ->  mk_eget file h (expression file e)
  | Tuple es -> Etuple (List.map (expression file) es)
  | Proj (i,e) -> Eproj(i, expression file e) 
  | Cnst c -> Ecnst (string_of_cnst file e.e_ty c)
  | App(Ifte,[e1;e2;e3]) -> 
    Eif(expression file e1, expression file e2, expression file e3)
  | App(op,es) ->
    Eapp(op_of_op file op, List.map (expression file) es)
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
  let init_res lc = 
    let e = expression file (init_res_expr osym.Osym.codom) in
    Iasgn([vres], e) :: lc in
  {
    f_name = "o" ^ Osym.to_string osym;
    f_param = List.map (fun v -> pvar [] v, v.Vsym.ty) param;
    f_local = (vres, osym.Osym.codom) :: 
      List.map (fun e ->  
        let v = destr_V e in 
        (pvar [] v, v.Vsym.ty)) (Se.elements (write_lcmds lc));
    f_res   = Some (vres, osym.Osym.codom);
    f_body  = init_res (body lc);
  }

let ginstr file adv = function
  | GLet (v,e) -> Iasgn ([pvar [] v],expression file e)
  | GSamp(v,(ty,r)) -> 
    Irnd ([pvar [] v], ty, List.map (expression file) r)
  | GCall(vs,a,e,_) -> Icall(List.map (pvar []) vs, (adv, "a"^Asym.to_string a),
                             expression file e)

let instructions file adv gdef =   
  List.map (ginstr file adv) gdef 

let oracles file oinfo = 
  { mod_name = "O";
    mod_param = [];
    mod_body = Mod_def 
      (List.rev 
      (Osym.H.fold (fun os oi l ->
        MCfun(oracle file (os, oi.oparams, oi.obody, oi.ores))::l) oinfo [])) }

let ensure_global file local g =
  let test = function
    | Cmod g' -> g.mod_name = g'.mod_name
    | _ -> false in
  if not local && not (List.exists test file.glob_decl) then
    let c = List.find test file.loca_decl in
    file.loca_decl <- List.filter (fun c -> not (test c)) file.loca_decl;
    file.glob_decl <- c :: file.glob_decl
      
    
let game ?(local=true) file g = 
  try 
    let g = snd (List.find (fun (g',_m) -> gdef_equal g g') file.game_trans) in
    ensure_global file local g;
    g
  with Not_found ->
    let ginfo = game_info g in
    add_adv local file ginfo;
    let globs = globals g in 
    let m_orcl = oracles file ginfo.oinfo in
    let alias = (mod_name "A" [mod_name "O" []]) in (* TODO add the H oracle *)
    let m_adv = {
      mod_name = "A";
      mod_param = [];
      mod_body = Mod_alias alias;
    } in
    let f_main = 
      { f_name = "main";
        f_param = [];
        f_local = [];
        f_res   = None;
        f_body  = instructions file (mod_name "A" []) g;
      } in
    let comp = 
      globs @ [MCmod m_orcl;
                       MCmod m_adv;
                       MCfun f_main] in
    let name = top_name file "M" in
    let modu = 
      { mod_name  = name;
        mod_param = [adv_decl file];
        mod_body  = Mod_def comp;
      } in
    file.game_trans <- (g,modu)::file.game_trans;
    if local then file.loca_decl <- Cmod(modu) :: file.loca_decl
    else file.glob_decl <- Cmod(modu) :: file.glob_decl;
    modu

let add_assumption file name assum = 
  let advty = top_name file ("Adv_"^name) in
  let ngame1 = top_name file ("G_"^name^string_of_int 1) in
  let ngame2 = top_name file ("G_"^name^string_of_int 2) in
  let pub = assum.ad_pubvars in
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
      f_param = [];
      f_local = (res,mk_Bool) :: vparams @ local;
      f_res = Some (res,mk_Bool);
      f_body = 
        init @
          [Icall([res], (mod_name "A" [], "main"), 
                 Etuple(List.map (fun v -> Epv(pvar [] v)) params))];
    } in
    { mod_name = name;
      mod_param = ["A", advty];
      mod_body = Mod_def [MCfun main];
    }, List.length init in 

  let g1, len1 = game ngame1 assum.ad_prefix1 in
  let g2, len2 = game ngame2 assum.ad_prefix2 in
  let info = {
    a_name  = assum.ad_name;
    a_priv  = assum.ad_privvars;
    a_param = params;
    a_advty = advty;
    a_cmd1  = g1;
    a_len1  = len1; 
    a_cmd2  = g2; 
    a_len2  = len2;
  } in
  Ht.add file.assump name info
  
let add_assumptions file ts = 
  Ht.iter (fun n a -> add_assumption file n a) ts.ts_assms_dec

let init_file ts pft = 
  let file = empty_file in
  add_lvars    file ts;
  add_gvars    file ts;
  add_bilinears file ts;
  add_hashs     file ts;
  add_assumptions file ts;
  let _ = game ~local:false file pft.pt_ju.ju_gdef in
  file

let extract_pr ?(local=true) file mem ju =
  let modm = game ~local file ju.ju_gdef in
  let modma = {mn = modm.mod_name; ma = [adv_mod file]} in
  let ev   = formula file [modm.mod_name] None ju.ju_ev in
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
  file.loca_decl <- Clemma(true, name,body,proof) :: file.loca_decl;
  name

let get_game file g = 
  try snd (List.find (fun (g',_m) -> gdef_equal g g') file.game_trans)
  with Not_found -> assert false

let pr_admit s fmt () =
  F.fprintf fmt "(* %s *) admit." s

let pp_swap side fmt (p,i) = 
  F.fprintf fmt "swap{%i} %i %i" side (p+1) i

let pp_swaps side fmt sw = 
  if sw <> [] then
    F.fprintf fmt "@[%a.@]@ " (pp_list ";@ " (pp_swap side)) sw

let init_same file ju1 ju2 = 
  let g1 = get_game file ju1.ju_gdef in
  let g2 = get_game file ju2.ju_gdef in
  let ev1 = formula file [g1.mod_name] (Some "1") ju1.ju_ev in  
  let ev2 = formula file [g2.mod_name] (Some "2") ju2.ju_ev in
  let ev  = f_eq ev1 ev2 in 
  let open_pp fmt () = 
    F.fprintf fmt "@[<v>intros &m;byequiv (_: ={glob A} ==> %a);@ "
      pp_form ev;
    F.fprintf fmt "  [ proc | by [] | by intros &m1 &m2 ->].@ " in
  let close_pp fmt () = 
    F.fprintf fmt "@]" in
  g1,g2,open_pp,close_pp

let pr_swap file sw ju1 ju2 fmt () =
  let _,_,open_pp, close_pp = init_same file ju1 ju2 in
  open_pp fmt ();
  pp_swaps 1 fmt sw;
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
  | TOr      of tactic * tactic
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

let t_algebra = TOr(Algebra, Smt)
let t_spa = TSeq [Skip;Progress [];t_algebra]
let t_pa  = TSeq [Progress [];t_algebra]
let t_aa  = TSeq [Auto;t_algebra]
let t_id  = TSeq []

let t_pr_if = 
  Tstring 
    "by (move=> &m1 &m2 H;rewrite -eq_iff;move: H;progress;(algebra || smt))"

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
  | Algebra   -> F.fprintf fmt "algebra"
  | Smt       -> F.fprintf fmt "smt"
  | Call inv  -> F.fprintf fmt "call (_:%a)" pp_form inv
  | If        -> F.fprintf fmt "if" 
  | Proc      -> F.fprintf fmt "proc"
  | Seq (i1,i2,f) -> 
    F.fprintf fmt "@[seq %i %i :@ (@[%a@])@]" i1 i2 pp_form f
  | Apply s   -> F.fprintf fmt "apply %s" s
  | TOr(t1,t2) -> F.fprintf fmt "(@[%a ||@ %a@])" pp_tac t1 pp_tac t2
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


let mk_eq_expr file ?(local=Vsym.S.empty) g1 g2 e =
  f_eq (formula file [g1.mod_name] (Some "1") ~local e)
       (formula file [g2.mod_name] (Some "2") ~local e)

let mk_eq_exprs file ?(local=Vsym.S.empty) g1 g2 es =
  match Se.elements es with
  | [] -> f_true
  | e::es -> 
    List.fold_left (fun eq e -> f_and (mk_eq_expr file ~local g1 g2 e) eq)
      (mk_eq_expr file ~local g1 g2 e) es

let pp_inv file ?(local=Vsym.S.empty) g fmt (x,inv) = 
  let flocal = Vsym.S.singleton x in
  let f = formula file [g.mod_name] (Some "2") ~local ~flocal inv in
  F.fprintf fmt "@[<hov 2>(fun (%a:%a),@ %a)@]"
    Vsym.pp x (pp_type file) x.Vsym.ty pp_form f 

let mu_x_def file fmt ty = 
  match ty.ty_node with
  | BS lv -> 
    F.fprintf fmt "%a.Dword.mu_x_def" pp_mod_name (mod_lvar file lv)
  | Bool ->
    F.fprintf fmt "Bool.Dbool.mu_x_def"
  | G _gv -> assert false (* FIXME *)
  | Fq    -> F.fprintf fmt "FDistr.mu_x_def_in"
  | Prod _ -> assert false (* FIXME *) 

let supp_def file fmt ty = 
  match ty.ty_node with
  | BS lv -> 
    F.fprintf fmt "%a.Dword.in_supp_def" pp_mod_name (mod_lvar file lv)
  | Bool ->
    F.fprintf fmt "Bool.Dbool.supp_def"
  | G _gv -> assert false (* FIXME *)
  | Fq    -> F.fprintf fmt "FDistr.supp_def"
  | Prod _ -> assert false (* FIXME *) 

let build_conv_proof file g1 g2 lc1 lc2 = 
  let add_info1 v1 e1 loc info = 
    add_let_info file g1 v1 e1 true loc info in
  let add_info2 v2 e2 loc info = 
    add_let_info file g2 v2 e2 false loc info in
  let add_rnd v1 v2 l1 l2 loc info = 
    add_rnd_info file g1 g2 v1 v2 l1 l2 loc info in
  let prove_orcl info (_,p1,lc1,_) (_,p2,lc2,_) =
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
    Tac (TSeq [Proc;TSeqSub (Seq(1,1,inv), [Auto; t_id])]) :: tacs in
        
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
      invs = List.fold_left f_and info.invs eqs } in
  (* the game are now ju ju' *)
  let rec aux lc1 lc2 info = 
    match lc1, lc2 with
    | [], [] -> info
    | GLet (v1,e1)::lc1, _ ->
      aux lc1 lc2 (add_info1 v1 e1 false info)
    | _, GLet (v2,e2)::lc2 ->
      aux lc1 lc2 (add_info2 v2 e2 false info)
    | GSamp(v1,(_,l1))::lc1, GSamp(v2,(_,l2))::lc2 ->
      aux lc1 lc2 (add_rnd v1 v2 l1 l2 false info) 
    | GCall(vs1,_,_,odef1)::lc1, GCall(vs2,_,_,odef2)::lc2 ->
      aux lc1 lc2 (add_call vs1 odef1 vs2 odef2 info)
    | _, _ -> assert false in
  let info = 
    { loc1 = Vsym.S.empty; loc2 = Vsym.S.empty;
      pos1 = 0; pos2 = 0;
      tacs = [Tac t_spa]; invs = f_true } in
  aux lc1 lc2 info 

let pr_conv file sw1 ju1 ju ju' ju2 sw2 fmt () = 
  let g1,g2,open_pp, close_pp = init_same file ju1 ju2 in
  open_pp fmt (); 
  F.fprintf fmt "(* conv rule *)@ ";
  pp_swaps 1 fmt sw1;
  pp_swaps 2 fmt (invert_swap sw2);
  let info = build_conv_proof file g1 g2 ju.ju_gdef ju'.ju_gdef in 
  pp_cmds fmt info.tacs;
  close_pp fmt ()

let pr_random file (pos,inv1,inv2) ju1 ju2 fmt () =
  let g1,g2,open_pp, close_pp = init_same file ju1 ju2 in
  (*let write = write_gcmds (Util.take pos ju2.ju_gdef) in
    let eqs = mk_eq_exprs file g1 g2 write in *)
  open_pp fmt ();
  let lc1 = Util.take pos ju1.ju_gdef in
  let lc2 = Util.take pos ju2.ju_gdef in
  let info =  build_conv_proof file g1 g2 lc1 lc2 in 
  F.fprintf fmt "sim.@ ";
  F.fprintf fmt "wp %i %i.@ " (pos + 1) (pos + 1);
  F.fprintf fmt "@[<hov 2>rnd@ %a@ %a.@]@ "
    (pp_inv file g2) inv2 (pp_inv file g2) inv1;
  F.fprintf fmt "@[<hov 2>conseq (_: _ ==>@ %a /\\ ={glob A}).@]@ " 
    pp_form info.invs;
  let ty = (fst inv1).Vsym.ty in 
  F.fprintf fmt "  progress.@ ";
  F.fprintf fmt "    by algebra.@ ";
  F.fprintf fmt "    by rewrite !%a.@ " (mu_x_def file) ty;
  F.fprintf fmt "    by apply %a.@ " (supp_def file) ty;
  F.fprintf fmt "    by algebra.@ ";
  pp_cmds fmt info.tacs;
  close_pp fmt ()

let pr_random_orcl file (pos, inv1, inv2) ju1 ju2 fmt () =
  let g1,g2,open_pp, close_pp = init_same file ju1 ju2 in
  let _i, ctxt = Game.get_ju_octxt ju1 pos in
  let _i, ctxt2 = Game.get_ju_octxt ju2 pos in
  let jctxt = ctxt.juoc_juc in
  let write1 = write_gcmds jctxt.juc_left in
  let writec = add_binding ctxt.juoc_avars in
  let write1c = Se.union write1 writec in
  let write2 = write_gcmds jctxt.juc_right in
  let write = Se.union write1c write2 in
  open_pp fmt ();
  F.fprintf fmt "conseq (_: _ ==> @[%a@]) => //.@ "
    pp_form (mk_eq_exprs file g1 g2 write);
  let len = List.length jctxt.juc_left in
  F.fprintf fmt "seq %i %i : (@[={glob A} /\\ %a@]);@ " len len
      pp_form (mk_eq_exprs file g1 g2 write1);
  F.fprintf fmt "  [ by sim | ].@ ";
  if jctxt.juc_right <> [] then begin
    F.fprintf fmt "seq %i %i : (@[={glob A} /\\ %a@]);@ " 
      1 1
      pp_form (mk_eq_exprs file g1 g2 write1c);
    F.fprintf fmt "  [ | by sim ].@ "
  end;
  F.fprintf fmt "call (_: @[%a@]).@ "
    pp_form (mk_eq_exprs file g1 g2 write1);
  List.iter (fun _ -> F.fprintf fmt "  sim.@ ") ctxt.juoc_oleft;
  (* The proof of the oracle *)
  let ginv = mk_eq_exprs file g1 g2 write1 in
  let p1 = ctxt.juoc_oargs and p2 = ctxt2.juoc_oargs in
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
  let info = aux ctxt.juoc_cleft ctxt2.juoc_cleft info in
  F.fprintf fmt "  proc;seq 1 1 : (@[%a@]);[by sim | ].@ "
    pp_form iinv;
  F.fprintf fmt "  @[%a@]@ " pp_cmds info.tacs;
  F.fprintf fmt "  sim.@ ";
  F.fprintf fmt "  wp 1 1.@ ";
  F.fprintf fmt "  @[<hov 2>rnd@ %a@ %a.@]@ "
    (pp_inv file ~local:info.loc2 g2) inv2 (pp_inv file ~local:info.loc2 g2)
    inv1;
  F.fprintf fmt "  @[<hov 2>conseq (_: _ ==>@ %a).@]@ " 
    pp_form info.invs;
  let ty = (fst inv1).Vsym.ty in 
  F.fprintf fmt "    progress.@ ";
  F.fprintf fmt "      by algebra.@ ";
  F.fprintf fmt "      by rewrite !%a.@ " (mu_x_def file) ty;
  F.fprintf fmt "      by apply %a.@ " (supp_def file) ty;
  F.fprintf fmt "      by algebra.@ ";
  F.fprintf fmt "    auto.@ ";

(* End proof of the oracle *)
  List.iter (fun _ -> F.fprintf fmt "  sim.@ ") ctxt.juoc_oright;
  F.fprintf fmt "auto.";
  close_pp fmt ()
  
  

let pr_intr_rw1_app lemma1 lemma2 fmt () = 
  F.fprintf fmt "intros &m; rewrite {1}(%s &m);apply (%s &m)."
    lemma1 lemma2 

let extract_assum file dir subst ainfo pft pft' =
  let g  = game file pft.pt_ju.ju_gdef in
  let g'  = game file pft'.pt_ju.ju_gdef in
  let ev = pft.pt_ju.ju_ev in
  let len = if dir = LeftToRight then ainfo.a_len1 else ainfo.a_len2 in
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
        ainfo.a_priv Sstring.empty in
    (* The private variables should be remove *)
    let tokeep = function
      | MCvar ((_,v),_) -> not (Sstring.mem v priv) 
      | _ -> true in
    let comp = List.filter tokeep comp in
    let main = 
      let mk_param v = 
        (([], "_" ^ Vsym.to_string v), v.Vsym.ty) in
      let param = List.map mk_param ainfo.a_param in
      let glob = List.map subst_v ainfo.a_param in
      let assign_global = 
        List.map2 (fun vg (v,_) -> Iasgn([pvar [] vg], Epv v)) glob param in
      let res = ([], "_res") in
      let dres = res, mk_Bool in
      let ev = expression file ev in
      { f_name = "main";
        f_param = param;
        f_local = [dres];
        f_res   = Some dres;
        f_body  = 
          assign_global @ 
            (* The head should be remove *)
            drop len f.f_body @ [Iasgn([res], ev)] } in
    let advname = top_name file ("Fadv_"^ainfo.a_name) in 
    { mod_name = advname;
      mod_param = g.mod_param;
      mod_body = Mod_def (comp @ [MCfun main]) } in
  file.glob_decl <- Cmod fadv :: file.glob_decl;
  let fa = mod_name fadv.mod_name [mod_name (adv_name file) []] in
  let a1 = mod_name ainfo.a_cmd1.mod_name [fa] in
  let a2 = mod_name ainfo.a_cmd2.mod_name [fa] in
  let pr = extract_pr file mem pft.pt_ju in
  let pr' = extract_pr file mem pft'.pt_ju in
  let pra1 = Fpr((a1,"main"), mem, [], Fv(([],"res"),None)) in
  let pra2 = Fpr((a2,"main"), mem, [], Fv(([],"res"),None)) in
  let pra, pra' = if dir = LeftToRight then pra1, pra2 else pra2, pra1 in
  let proof_ass g ev fmt () = 
    let ev = formula file [g.mod_name] (Some "1") ev in
    F.fprintf fmt 
      "@[<v> intros &m; byequiv (_: @[={glob A} ==>@ %a@]) => //.@ "
      pp_form (f_eq ev (Fv(([], "res"), Some "2")));
    F.fprintf fmt
      "by proc; inline{2} %a; wp; sim.@]"
      pp_fun_name (fa,"main") in
  let lemma = 
    add_pr_lemma file (mk_cmp pr cmp_eq pra) 
      (Some (proof_ass g pft.pt_ju.ju_ev)) in
  let lemma' = 
    add_pr_lemma file (mk_cmp pr' cmp_eq pra') 
      (Some (proof_ass g' pft'.pt_ju.ju_ev)) in
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
    match List.rev ju.ju_gdef with GSamp(_,d) :: _ -> d | _ -> assert false in
  let size, lemma =
    match ty.ty_node with
    | BS lv -> f_2pow (bs_length file lv), lvar_mod file lv ^".Dword.mu_x_def"
    | Bool  -> f_2  , "Bool.Dbool.mu_x_def"
    | G _   -> f_Fq,  assert false (* FIXME *)
    | Fq    -> f_Fq,  "F.FDistr.mu_x_def_in"
    | _     -> assert false (* FIXME *) in
  let isize = f_rinv (Frofi size) in
  assert (l = []);
  let evs = destruct_Land ju.ju_ev in
  let ev = List.nth evs pos in
  if is_Eq ev then isize, ev, lemma 
  else assert false (* FIXME exists *)

let extract_rnd_indep file side pos ju = 
  let g = game file ju.ju_gdef in
  let pr = extract_pr file mem ju in
  let bound, ev, lemma = bound_rnd_indep file pos ju in
  let proof fmt () = 
    F.fprintf fmt "@[<v>intros &m; byphoare (_ : true ==> %a) => //.@ "
      pp_form (formula file [g.mod_name] None ev);
    if is_Eq ev then
      let e1,e2 = destr_Eq ev in
      let e = if side then e2 else e1 in
      F.fprintf fmt 
        "proc; rnd ((=) %a); conseq (_ : _ ==> true); last by [].@ "
        pp_form (formula file [g.mod_name] None e);
      F.fprintf fmt "simplify; intros &m1;progress.@ ";
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
  let g = game file pft.pt_ju.ju_gdef in 
  let g' = game file pft'.pt_ju.ju_gdef in
  let side, adv =
    let comp = match g.mod_body with 
      | Mod_def cmp -> cmp 
      | _ -> assert false in
    let comp, f = 
      match List.rev comp with 
      | MCfun f :: r -> List.rev r, f
      | _ -> assert false in
   
    let side, x, ex =
      match List.nth ju.ju_gdef pos, List.nth ju'.ju_gdef pos with 
      | GSamp(x,(_ty,[])), GSamp(x',(_ty',[e])) -> 
        assert (Vsym.equal x x'); (* FIXME: check ty *)
        `LeftToRight, x, e
      | GSamp(x,(_ty,[e])), GSamp(x',(_ty',[])) ->
        assert (Vsym.equal x x');
        `RightToLeft, x, e
      | _, _ -> assert false in
    let hd,_,tl = Util.split_n pos f.f_body in
    let a1 = 
      let res = ([], "_res") in
      let dres = res, mk_Fq in
      let ex = expression file ex in
      { f_name = "a1";
        f_param = [];
        f_local = [dres];
        f_res   = Some dres;
        f_body  = List.rev_append hd [Iasgn([res],ex)] } in
    let a2 = 
      let arg = ([], "_arg") in
      let darg = arg, mk_Fq in
      {
        f_name = "a2";
        f_param = [darg];
        f_local = [];
        f_res   = None;
        f_body  = Iasgn([pvar [] x], Epv arg)::tl } in
    let advname = top_name file ("SDadv") in 
    side, { mod_name = advname;
      mod_param = [];
      mod_body = Mod_def (comp @ [MCfun a1; MCfun a2]) } in
  file.loca_decl <- Cmod adv :: file.loca_decl;

  let eps = f_rinv (Frofi f_Fq) in
  let bound = f_radd pr' (f_rinv (Frofi f_Fq)) in
  let pr1, pr2 = if side = `LeftToRight then pr, pr' else pr', pr in
  let g1, g2 = if side = `LeftToRight then g, g' else g', g in

  let proof fmt () = 
    F.fprintf fmt "intros &m.@ ";
    let ev = formula file [adv.mod_name] None ju.ju_ev in 
    let mk_eqs g fv = 
      let mk_eq e = 
        f_eq (formula file [g] (Some "1") e) 
          (formula file [adv.mod_name] (Some "2") e) in
      match Se.elements fv with
      | [] -> f_true
      | e :: es -> List.fold_left (fun f e -> f_and f (mk_eq e)) (mk_eq e) es in
    let fv = Expr.e_vars ju.ju_ev in
    F.fprintf fmt 
      "cut -> : @[%a =@ Pr[SDF.SD1query.SD1(%s, S).main() @@ &m :@ %a]@].@ " 
      pp_form pr1 adv.mod_name pp_form ev;
    F.fprintf fmt "byequiv (_ : ={glob A} ==> %a) => //. @ "
      pp_form (mk_eqs g1.mod_name fv);
    F.fprintf fmt "  proc;inline *;sim.@ ";
    
    F.fprintf fmt 
      "cut -> : @[%a =@ Pr[SDF.SD1query.SD1(%s, SE).main() @@ &m :@ %a]@].@ " 
      pp_form pr2 adv.mod_name pp_form ev;
    F.fprintf fmt "byequiv (_ : ={glob A} ==> %a) => //. @ "
      pp_form (mk_eqs g2.mod_name fv);
    F.fprintf fmt "  proc;inline *;sim.@ ";
    F.fprintf fmt "  rnd; wp %i %i => /=.@ " pos (pos + 1);
    F.fprintf fmt "  conseq (_ : _ ==> ={glob A} /\\ %a) => //.@ "
    pp_form (mk_eqs g2.mod_name (write_gcmds (Util.take pos ju.ju_gdef)));
    F.fprintf fmt "  sim.@ ";
    F.fprintf fmt "pose EV := fun (g:glob %s) (u:unit),@ " adv.mod_name;
    List.iter (fun e -> 
      let v = destr_V e in
      F.fprintf fmt "  let %a = g.`%s.%a in@ "
        Vsym.pp v adv.mod_name Vsym.pp v) (Se.elements fv);
    F.fprintf fmt "  @[%a@].@ "
      pp_form (formula file [] None ju.ju_ev);
    F.fprintf fmt "apply (SDField.%s %s &m EV)." 
      (if side = `LeftToRight then "SD1_conseq_add" else "SD1_conseq_add_E")
      adv.mod_name
  in
  
  let lemma = add_pr_lemma file (mk_cmp pr cmp_le bound) (Some proof) in
  lemma, pr, cmp_le, eps
  
let default_proof file mem s pft = 
  F.eprintf "WARNING rule %s not extracted@." s;
  let pr = extract_pr ~local:false file mem pft.pt_ju in
  let lemma = add_pr_lemma file (mk_cmp pr cmp_eq pr) 
    (Some (fun fmt () -> 
      F.fprintf fmt "(* %s *)@ " s;
      F.fprintf fmt "trivial.@ ")) in
  lemma, pr, cmp_eq, pr 

let rec extract_proof file pft = 
  match pft.pt_rule with
  | Rconv -> extract_conv file pft [] pft

  | Rctxt_ev _ ->
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 file pft pft' (pr_admit "ctxt_ev")

  | Rremove_ev _ -> assert false

  | Rmerge_ev _ -> 
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 file pft pft' (pr_admit "merge_ev")

  | Rrnd (pos,_,inv1,inv2) ->

    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 file pft pft' 
      (pr_random file (pos,inv1,inv2) pft.pt_ju pft'.pt_ju)

  | Rrnd_orcl (pos, inv1, inv2) ->
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 file pft pft' 
      (pr_random_orcl file (pos,inv1,inv2) pft.pt_ju pft'.pt_ju)

  | Rswap _ ->
    let sw1, pft' = skip_swap pft in
    begin match pft'.pt_rule with
    | Rconv -> extract_conv file pft sw1 pft'
    | _ ->
      (* FIXME *)
      extract_proof_sb1 file pft pft' (pr_swap file sw1 pft.pt_ju pft'.pt_ju)
    end
  | Rswap_orcl _ ->
    let pft' = List.hd pft.pt_children in
    extract_proof_sb1 file pft pft' (pr_admit "swap oracle")

  | Rrnd_indep (side, pos) -> 
    extract_rnd_indep file side pos pft.pt_ju 
    
  | Rassm_dec (dir,subst, assum) ->
    let pft' = List.hd pft.pt_children in
    let (lemma1, pr',cmp,bound) = extract_proof file pft' in
    let ainfo = 
      try Ht.find file.assump assum.ad_name with Not_found -> assert false in
    let lemma2, pr, abs = extract_assum file dir subst ainfo pft pft' in
    let proof fmt () = 
      F.fprintf fmt "@[<v>intros &m.@ ";
      F.fprintf fmt "@[apply (real_le_trans@ %a@ %a@ %a).@]@ "
        (pp_form_lvl min_lvl) pr 
        (pp_form_lvl min_lvl) (f_radd abs pr') 
        (pp_form_lvl min_lvl) (f_radd abs bound);
      F.fprintf fmt "apply (%s &m).@ " lemma2;
      F.fprintf fmt "apply Real.addleM; first by [].@ ";
      F.fprintf fmt "by %s (%s &m).@]"
        (if cmp = cmp_eq then "rewrite" else "apply") lemma1 in
    let bound = f_radd abs bound in
    let lemma3 = 
      add_pr_lemma file (mk_cmp pr cmp_le bound) (Some proof) in
    lemma3, pr, cmp_le, bound 

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
        (pp_form_lvl min_lvl) (f_radd pr' eps);
      F.fprintf fmt "apply (%s &m).@ " lemma2;
      F.fprintf fmt "apply Real.addleM; last by [].@ ";
      F.fprintf fmt "by %s (%s &m).@]"
        (if cmp = cmp_eq then "rewrite" else "apply") lemma1 in
    let lemma3 = 
      add_pr_lemma file (mk_cmp pr cmp_le bound) (Some proof) in
    lemma3, pr, cmp_le, bound 

  | Rexc_orcl _ -> default_proof file mem "exc_orl" pft
  | Radd_test _ -> default_proof file mem "add_test" pft
  | Rrw_orcl _  -> default_proof file mem "rw_orcl" pft
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

  | Rassm_comp _ -> default_proof file mem "assm_comp" pft
  | Rcase_ev _ -> default_proof file mem "case_ev" pft
  | Rsplit_ev _ -> default_proof file mem "split_ev" pft
  | Rrw_ev (_, _) -> default_proof file mem "rw_ev" pft
    
 
    

and extract_conv file pft sw1 pft1 =
  let pft2 = skip_conv pft1 in
  let sw2, pft' = skip_swap pft2 in 
  extract_proof_sb1 file pft pft' 
    (pr_conv file sw1 pft.pt_ju pft1.pt_ju pft2.pt_ju pft'.pt_ju sw2)

and extract_proof_sb1 file pft pft' proof = 
  let (lemma1, pr',cmp,bound) = extract_proof file pft' in
  let pr = extract_pr file mem pft.pt_ju in
  let lemma2 = 
    add_pr_lemma file (mk_cmp pr cmp_eq pr') 
      (Some proof) in
  let lemma3 = 
    add_pr_lemma file (mk_cmp pr cmp bound) 
      (Some (pr_intr_rw1_app lemma2 lemma1)) in
  lemma3, pr, cmp, bound
  

let extract_file ts = 
  let pt = get_proof_tree ts in
  let pft = Rules.simplify_proof_tree pt in
  let file = init_file ts pft in
  let lemma, pr, cmp, bound = extract_proof file pft in
  let name = top_name file "conclusion" in
  let body = forall_mem (mk_cmp pr cmp bound) in
  let proof fmt () = 
    F.fprintf fmt "apply %s." lemma in
    
  file.loca_decl <- Clemma(false, name,body, Some proof) :: file.loca_decl;
  file

let extract ts filename = 
  let file = extract_file ts in
  let out = open_out filename in
  let fmt = F.formatter_of_out_channel out in
  Printer.pp_file fmt file;
  close_out out






















