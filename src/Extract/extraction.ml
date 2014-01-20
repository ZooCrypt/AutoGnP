open Util
open Type
open Expr 
open Game 
open Assumption
open TheoryState 
open CoreRules
open File
open Printer

module Ht = Hashtbl



(** game translation *)

let pvar modn v = 
  modn, Vsym.tostring v

let globals gdef = 
  let glob = gdef_vars gdef in
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
  | Not     -> "!"
  | Ifte    -> assert false
  | EMap _  -> assert false

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
  
let string_of_cnst file ty = function
  | GGen   -> fsprintf "%s.g" (gvar_mod file (destr_G ty)) |> fsget
  | FNat i -> fsprintf "(F.ofint %i)" i |> fsget
  | Z      -> fsprintf "%s.zeros" (lvar_mod file (destr_BS ty)) |> fsget
  | B b    -> fsprintf "%b" b |> fsget

let rec expression file e = 
  match e.e_node with 
  | V v -> Epv (pvar [] v)
  | H(h,e) ->  mk_eget file h (expression file e)
  | Tuple es -> Etuple (List.map (expression file) es)
  | Proj (i,e) -> Eproj(i, expression file e) 
  | Cnst c -> Ecnst (string_of_cnst file e.e_ty c)
  | App(Eq,[e1;e2]) -> 
    Eeq(expression file e1, expression file e2)
  | App(Ifte,[e1;e2;e3]) -> 
    Eif(expression file e1, expression file e2, expression file e3)
  | App(op,es) ->
    Eapp(string_of_op file op, List.map (expression file) es)
  | Nary(op,es) -> 
    begin match es with
    | [] -> assert false
    | e::es -> 
      let op = string_of_nop file e.e_ty op in
      List.fold_left (fun e e1 -> Eapp(op,[e;expression file e1])) 
        (expression file e) es 
    end
  | Exists _ -> assert false 

let rec formula file prefix mem ?(local=Vsym.S.empty) e = 
  match e.e_node with 
  | V v -> 
    if Vsym.S.mem v local then Fv(pvar [] v, None)
    else Fv (pvar prefix v, mem)
  | H(h,e) ->  mk_fget file mem h (formula file prefix mem ~local e)
  | Tuple es -> Ftuple (List.map (formula file prefix mem ~local) es)
  | Proj (i,e) -> Fproj(i, formula file prefix mem ~local e) 
  | Cnst c -> Fcnst (string_of_cnst file e.e_ty c)
  | App(Eq,[e1;e2]) -> 
    Feq(formula file prefix mem ~local e1, formula file prefix mem ~local e2)
  | App(Ifte,[e1;e2;e3]) -> 
    Fif(formula file prefix mem ~local e1, 
        formula file prefix mem ~local e2, 
        formula file prefix mem ~local e3)
  | App(op,es) ->
    Fapp(string_of_op file op, List.map (formula file prefix mem ~local) es)
  | Nary(op,es) -> 
    begin match es with
    | [] -> assert false
    | e::es -> 
      let op = string_of_nop file e.e_ty op in
      List.fold_left 
        (fun e e1 -> Fapp(op,[e;formula file prefix mem ~local e1])) 
        (formula file prefix mem ~local e) es 
    end
  | Exists _ -> assert false 
  

let oracle file (osym,param,lc,ret) = 
  let res = "_res" in
  let vres = [],res in
  let rec body lc = 
    match lc with
    | [] -> [Iasgn([vres], Eapp("Some", [expression file ret]))]
    | LLet (v,e) :: lc -> 
      Iasgn ([pvar [] v],expression file e) :: body lc
    | LSamp (v,(ty,r)) :: lc -> assert (r = []); 
      Irnd ([pvar [] v], ty) :: body lc
    | LBind (_vs, _h) :: _ -> assert false 
    (*      while (res <> None && dom <> []) {
            e = hd dom;
            dom = tl dom;
            vs = h.[e];
            body
            } *)
    | LGuard e :: lc-> [Iif (expression file e, body lc, [])] in
  {
    f_name = Osym.tostring osym;
    f_param = List.map (fun v -> pvar [] v, v.Vsym.ty) param;
    f_local = List.map (fun e ->  
      let v = destr_V e in 
      (pvar [] v, v.Vsym.ty)) (Se.elements (write_lcmds lc));
    f_res   = Some (vres, osym.Osym.codom);
    f_body  = body lc;
  }

let ginstr file adv = function
  | GLet (v,e) -> Iasgn ([pvar [] v],expression file e)
  | GSamp(v,(ty,r)) -> assert (r = []); Irnd ([pvar [] v], ty)
  | GCall(vs,a,e,_) -> Icall(List.map (pvar []) vs, (adv, "a"^Asym.tostring a),
                             expression file e)

let instructions file adv gdef =   
  List.map (ginstr file adv) gdef 

let oracles file oinfo = 
  { mod_name = "O";
    mod_param = [];
    mod_body = Mod_def 
      (Osym.H.fold (fun os oi l ->
        MCfun(oracle file (os, oi.oparams, oi.obody, oi.ores))::l) oinfo []) }

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
    let name = top_name file "Game" in
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
        (pvar [] v, v.Vsym.ty) :: l) (gdef_vars gdef) [] in 

    let res = ([],"_res") in
    let init = instructions file (mod_name "A" []) gdef in
    let main = {
      f_name = "main";
      f_param = [];
      f_local = (res, mk_Bool) :: vparams @ local;
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
  Ht.iter (fun n a -> add_assumption file n a) ts.ts_assms

let init_file ts pft = 
  let file = empty_file in
  add_lvars    file ts;
  add_gvars    file ts;
  add_bilinears file ts;
  add_hashs     file ts;
  add_assumptions file ts;
  let _ = game ~local:false file pft.dr_ju.ju_gdef in
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
  if cmp = cmp_eq then Feq(f1,f2) else Fle(f1,f2)
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
  Format.fprintf fmt "(* %s *) admit." s

let pp_swap side fmt (p,i) = 
  Format.fprintf fmt "swap{%i} %i %i" side (p+1) i

let pp_swaps side fmt sw = 
  if sw <> [] then
    Format.fprintf fmt "@[%a.@]@ " (pp_list ";@ " (pp_swap side)) sw

let init_same file ju1 ju2 = 
  let g1 = get_game file ju1.ju_gdef in
  let g2 = get_game file ju2.ju_gdef in
  let ev1 = formula file [g1.mod_name] (Some "1") ju1.ju_ev in  
  let ev2 = formula file [g2.mod_name] (Some "2") ju2.ju_ev in
  let ev  = Feq(ev1, ev2) in 
  let open_pp fmt () = 
    Format.fprintf fmt "@[<v>intros &m;byequiv (_: ={glob A} ==> %a);@ "
      pp_form ev;
    Format.fprintf fmt "  [ proc | by [] | by intros &m1 &m2 ->].@ " in
  let close_pp fmt () = 
    Format.fprintf fmt "@]" in
  g1,g2,open_pp,close_pp

let pr_swap file sw ju1 ju2 fmt () =
  let _,_,open_pp, close_pp = init_same file ju1 ju2 in
  open_pp fmt ();
  pp_swaps 1 fmt sw;
  Format.fprintf fmt "sim.";
  close_pp fmt ()

let invert_swap sw = 
  List.fold_left (fun sw (p,i) -> (p+i, -i)::sw) [] sw

let pr_conv file sw1 ju1 _ju _ju' ju2 sw2 fmt () = 
  let _,_,open_pp, close_pp = init_same file ju1 ju2 in
  open_pp fmt (); 
  pp_swaps 1 fmt sw1;
  pp_swaps 2 fmt (invert_swap sw2);
  (* the game are now ju ju' *)
  Format.fprintf fmt "(* conv *)admit.";
  close_pp fmt ()

let pr_random file (pos,inv1,inv2,_newx) ju1 ju2 fmt () =
  let g1,g2,open_pp, close_pp = init_same file ju1 ju2 in
  let write = write_gcmds (Util.take pos ju2.ju_gdef) in
  let mk_eq e =
    let v = destr_V e in
    Feq(Fv(pvar [g1.mod_name] v, Some "1"),
        Fv(pvar [g2.mod_name] v, Some "2")) in
  let eqs = 
    match Se.elements write with
    | [] -> f_true
    | e::es -> List.fold_left (fun eq e -> f_and (mk_eq e) eq) (mk_eq e) es in
  let pp_inv fmt (x,inv) = 
    let local = Vsym.S.singleton x in
    Format.fprintf fmt "@[<hov 2>(fun %a,@ %a)@]"
      Vsym.pp x pp_form (formula file [g2.mod_name] (Some "2") ~local inv) in
  open_pp fmt ();
  Format.fprintf fmt "sim.@ ";
  Format.fprintf fmt "wp %i %i.@ " (pos + 1) (pos + 1);
  Format.fprintf fmt "@[<hov 2>rnd@ %a@ %a.@]@ "
    pp_inv inv2 pp_inv inv1;
  Format.fprintf fmt "@[<hov 2>conseq (_: _ ==>@ %a /\\ ={glob A}).@]@ " 
    pp_form eqs;
  Format.fprintf fmt "  progress.@ ";
  Format.fprintf fmt "    by smt. (* improve *)@ ";
  Format.fprintf fmt "    by smt. (* improve *)@ ";
  Format.fprintf fmt "    by ringeq. (* FIXME *)@ ";
  Format.fprintf fmt "    by ringeq. (* FIXME *)@ ";
  Format.fprintf fmt "  by apply eq_sym.@ ";
  Format.fprintf fmt "sim.";
  close_pp fmt ()

let pr_intr_rw1_app lemma1 lemma2 fmt () = 
  Format.fprintf fmt "intros &m; rewrite {1}(%s &m);apply (%s &m)."
    lemma1 lemma2 

let extract_assum file dir subst ainfo pft pft' =
  let g  = game file pft.dr_ju.ju_gdef in
  let g'  = game file pft'.dr_ju.ju_gdef in
  let ev = pft.dr_ju.ju_ev in
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
      Vsym.S.fold (fun v p -> Sstring.add (Vsym.tostring (subst_v v)) p)
        ainfo.a_priv Sstring.empty in
    (* The private variables should be remove *)
    let tokeep = function
      | MCvar ((_,v),_) -> not (Sstring.mem v priv) 
      | _ -> true in
    let comp = List.filter tokeep comp in
    let main = 
      let mk_param v = 
        (([], "_" ^ Vsym.tostring v), v.Vsym.ty) in
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
  let pr = extract_pr file mem pft.dr_ju in
  let pr' = extract_pr file mem pft'.dr_ju in
  let pra1 = Fpr((a1,"main"), mem, [], Fv(([],"res"),None)) in
  let pra2 = Fpr((a2,"main"), mem, [], Fv(([],"res"),None)) in
  let pra, pra' = if dir = LeftToRight then pra1, pra2 else pra2, pra1 in
  let proof_ass g ev fmt () = 
    let ev = formula file [g.mod_name] (Some "1") ev in
    Format.fprintf fmt 
      "@[<v> intros &m; byequiv (_: @[={glob A} ==>@ %a@]) => //.@ "
      pp_form (Feq(ev,Fv(([], "res"), Some "2")));
    Format.fprintf fmt
      "by proc; inline{2} %a; wp; sim.@]"
      pp_fun_name (fa,"main") in
  let lemma = 
    add_pr_lemma file (mk_cmp pr cmp_eq pra) 
      (Some (proof_ass g pft.dr_ju.ju_ev)) in
  let lemma' = 
    add_pr_lemma file (mk_cmp pr' cmp_eq pra') 
      (Some (proof_ass g' pft'.dr_ju.ju_ev)) in
  let abs = Fabs (f_rsub pra1 pra2) in
  let proof fmt () = 
    Format.fprintf fmt 
      "intros &m;rewrite (%s &m) (%s &m);apply ZooUtil.le_abs_add%i."  
      lemma lemma' (if dir = LeftToRight then 1 else 2) in
  let concl = 
    add_pr_lemma file 
      (mk_cmp pr cmp_le (f_radd abs pr'))
      (Some proof) in
  concl, pr, abs 

let rec skip_conv pft = 
  match pft.dr_rule with
  | Rconv -> skip_conv (List.hd pft.dr_subgoal)
  | _ -> pft

let skip_swap pft = 
  let rec aux sw pft = 
    match pft.dr_rule with
    | Rswap(p,i) -> aux ((p,i)::sw) (List.hd pft.dr_subgoal)
    | _ -> List.rev sw, pft in
  aux [] pft

let rec extract_proof file pft = 
  match pft.dr_rule with
  | Rconv -> extract_conv file pft [] pft
  | Rctxt_ev _ ->
    let pft' = List.hd pft.dr_subgoal in
    extract_proof_sb1 file pft pft' (pr_admit "ctxt_ev")
  | Rremove_ev _ -> assert false
  | Rmerge_ev _ -> 
    let pft' = List.hd pft.dr_subgoal in
    extract_proof_sb1 file pft pft' (pr_admit "merge_ev")
  | Rrandom (pos,inv1,inv2,newx) ->
    let pft' = List.hd pft.dr_subgoal in
    extract_proof_sb1 file pft pft' 
      (pr_random file (pos,inv1,inv2,newx) pft.dr_ju pft'.dr_ju)
  | Rrnd_orcl _ ->
    let pft' = List.hd pft.dr_subgoal in
    extract_proof_sb1 file pft pft' (pr_admit "random oracle")
  | Rexcept _ -> assert false
  | Rexc_orcl _ -> assert false 
  | Radd_test _ -> assert false 
  | Rrw_orcl _ -> assert false 
  | Rbad     _ -> assert false
  | Rswap _ ->
    let sw1, pft' = skip_swap pft in
    begin match pft'.dr_rule with
    | Rconv -> extract_conv file pft sw1 pft'
    | _ ->
      (* FIXME *)
      extract_proof_sb1 file pft pft' (pr_swap file sw1 pft.dr_ju pft'.dr_ju)
    end
  | Rswap_orcl _ ->
    let pft' = List.hd pft.dr_subgoal in
    extract_proof_sb1 file pft pft' (pr_admit "swap oracle")
  | Rrnd_indep _ -> (* FIXME *)
    let pr = extract_pr ~local:false file mem pft.dr_ju in
    let lemma = add_pr_lemma file (mk_cmp pr cmp_eq pr) 
      (Some (fun fmt () -> Format.fprintf fmt "(* rnd indep *)trivial.")) in
    lemma, pr, cmp_eq, pr
  | Rassm_dec (dir,subst, assum) ->
    let pft' = List.hd pft.dr_subgoal in
    let (lemma1, pr',cmp,bound) = extract_proof file pft' in
    let ainfo = 
      try Ht.find file.assump assum.ad_name with Not_found -> assert false in
    let lemma2, pr, abs = extract_assum file dir subst ainfo pft pft' in
    let proof fmt () = 
      Format.fprintf fmt "@[<v>intros &m.@ ";
      Format.fprintf fmt "@[apply (real_le_trans@ %a@ %a@ %a).@]@ "
        pp_form pr pp_form (f_radd abs pr') pp_form (f_radd abs bound);
      Format.fprintf fmt "apply (%s &m); apply Real.addleM; first by [].@ "
        lemma2;
      Format.fprintf fmt "by %s (%s &m).@]"
        (if cmp = cmp_eq then "rewrite" else "apply") lemma1 in
    let lemma3 = 
      add_pr_lemma file (mk_cmp pr cmp_le (f_radd abs bound)) (Some proof) in
    lemma3, pr, cmp_le, (f_radd abs bound)
    
  | _ -> 
    let pr = extract_pr ~local:false file mem pft.dr_ju in
    let lemma = add_pr_lemma file (mk_cmp pr cmp_eq pr) 
      (Some (fun fmt () -> Format.fprintf fmt "trivial.")) in
    lemma, pr, cmp_eq, pr

and extract_conv file pft sw1 pft1 =
  let pft2 = skip_conv pft1 in
  let sw2, pft' = skip_swap pft2 in 
  extract_proof_sb1 file pft pft' 
    (pr_conv file sw1 pft.dr_ju pft1.dr_ju pft2.dr_ju pft'.dr_ju sw2)

and extract_proof_sb1 file pft pft' proof = 
  let (lemma1, pr',cmp,bound) = extract_proof file pft' in
  let pr = extract_pr file mem pft.dr_ju in
  let lemma2 = 
    add_pr_lemma file (mk_cmp pr cmp_eq pr') 
      (Some proof) in
  let lemma3 = 
    add_pr_lemma file (mk_cmp pr cmp bound) 
      (Some (pr_intr_rw1_app lemma2 lemma1)) in
  lemma3, pr, cmp, bound
  

let extract_file ts = 
  let ps = get_proof_state ts in
  let pft = get_proof ps in
  let file = init_file ts pft in
  let lemma, pr, cmp, bound = extract_proof file pft in
  let name = top_name file "conclusion" in
  let body = forall_mem (mk_cmp pr cmp bound) in
  let proof fmt () = 
    Format.fprintf fmt "apply %s." lemma in
    
  file.loca_decl <- Clemma(false, name,body, Some proof) :: file.loca_decl;
  file

let extract ts filename = 
  let file = extract_file ts in
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  Printer.pp_file fmt file;
  close_out out






















