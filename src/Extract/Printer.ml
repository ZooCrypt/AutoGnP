open Util
open Type
open Expr
open File

(* -------------------------------------------------------------------- *)
let pp_if c pp1 pp2 fmt x =
  match c with
  | true  -> pp1 fmt x
  | false -> pp2 fmt x

let pp_maybe c tx pp fmt x =
  pp_if c (tx pp) pp fmt x

let pp_enclose ~pre ~post pp fmt x =
  F.fprintf fmt "%(%)%a%(%)" pre pp x post

let pp_paren pp fmt x =
  pp_enclose ~pre:"(" ~post:")" pp fmt x

let maybe_paren outer inner pp =
  pp_maybe (outer < inner) pp_paren pp
    
let next_lvl lvl = lvl + 10
let   min_lvl = 0       
let  proj_lvl = next_lvl min_lvl 
let   app_lvl = next_lvl proj_lvl
let   pow_lvl = next_lvl app_lvl 
let   opp_lvl = next_lvl pow_lvl 
let   mul_lvl = next_lvl opp_lvl 
let   add_lvl = next_lvl mul_lvl 
let    eq_lvl = next_lvl add_lvl 
let   not_lvl = next_lvl eq_lvl
let   and_lvl = next_lvl not_lvl 
let    if_lvl = next_lvl and_lvl 
let quant_lvl = next_lvl if_lvl 
let   max_lvl = max_int 
  
let pp_infix pp lvl op e1 e2 fmt () = 
  F.fprintf fmt "@[%a %s@ %a@]" (pp lvl) e1 op (pp (lvl-1)) e2
let pp_eq pp op e1 e2 fmt () = 
  F.fprintf fmt "@[%a %s@ %a@]" (pp (eq_lvl-1)) e1 op (pp (eq_lvl-1)) e2

(* -------------------------------------------------------------------- *)

let pp_pvar fmt (ms,s) =
  if ms = [] then F.fprintf fmt "%s" s
  else F.fprintf fmt "%a.%s" (pp_list "." F.pp_print_string) ms s

let pp_mem fmt s = F.fprintf fmt "&%s" s

let rec pp_mod_name fmt mn = 
  if mn.ma = [] then F.fprintf fmt "%s" mn.mn
  else 
    F.fprintf fmt "%s(@[<hov 1>%a@])" 
      mn.mn (pp_list ",@ " pp_mod_name) mn.ma

let pp_fun_name fmt (mn,s) = 
  F.fprintf fmt "%a.%s" pp_mod_name mn s

let pp_tvar fmt i = 
  let m =  {mn = i.tvar_mod; ma = []} in
  F.fprintf fmt "%a.%s" pp_mod_name m i.tvar_ty

let rec pp_type file fmt ty = 
 match ty.ty_node with
  | BS lv    -> pp_tvar fmt (get_lvar file lv)
  | Bool     -> F.fprintf fmt "bool"
  | G gv     -> pp_tvar fmt (get_gvar file gv)
  | Fq       -> F.fprintf fmt "F.t"
  | Prod tys ->
    if tys = [] then 
      F.fprintf fmt "unit"
    else
      F.fprintf fmt "(@[%a@])" (pp_list " *@ " (pp_type file)) tys

let pp_at_mem fmt = function
  | None -> ()
  | Some m -> F.fprintf fmt "{%s}" m

let rec pp_form_lvl outer fmt = function
  | Fv (v, m)     -> F.fprintf fmt "%a%a" pp_pvar v pp_at_mem m 
  | Ftuple es     ->
    F.fprintf fmt "(@[<hov 1>%a@])" (pp_list ",@ " pp_form) es
  | Fproj (i,e)   ->
    let pp fmt e = 
      F.fprintf fmt "%a.`%i" (pp_form_lvl proj_lvl) e i in
    maybe_paren outer proj_lvl pp fmt e
  | Fcnst c       -> F.fprintf fmt "%s" c
  | Fapp(op,es)   -> 
    let pp, inner = 
      match op, es with
      | Oopp, [e] -> 
        let pp fmt () = 
          F.fprintf fmt "@[-@ %a@]" (pp_form_lvl opp_lvl) e in
        pp, opp_lvl
      | Onot, [e] ->
        let pp fmt () = 
          F.fprintf fmt "@[!@ %a@]" (pp_form_lvl not_lvl) e in
        pp, not_lvl
      | Opow, [e1;e2] -> pp_infix pp_form_lvl pow_lvl "^" e1 e2, pow_lvl
      | Osub, [e1;e2] -> pp_infix pp_form_lvl add_lvl "-" e1 e2, add_lvl
      | Oadd, [e1;e2] -> pp_infix pp_form_lvl add_lvl "+" e1 e2, add_lvl
      | Omul, [e1;e2] -> pp_infix pp_form_lvl mul_lvl "*" e1 e2, mul_lvl
      | Odiv, [e1;e2] -> pp_infix pp_form_lvl mul_lvl "/" e1 e2, mul_lvl
      | Oeq,  [e1;e2] -> pp_eq    pp_form_lvl         "=" e1 e2, eq_lvl
      | Ole,  [e1;e2] -> pp_eq    pp_form_lvl         "<=" e1 e2, eq_lvl
      | Oand, [e1;e2] -> pp_infix pp_form_lvl mul_lvl "/\\" e1 e2, and_lvl
      | (Oopp | Opow | Oadd | Osub | Omul | Odiv | Oeq | Ole | Oand | Onot), _ -> 
        assert false
      | Ostr op, es ->
        let pp fmt () = 
          F.fprintf fmt "@[<hov 2>%s@ %a@]" op 
            (pp_list "@ " (pp_form_lvl (app_lvl - 1))) es in
        pp, app_lvl
 
    in
    maybe_paren outer inner pp fmt ()
  | Fif(e1,e2,e3) ->
    let pp fmt () = 
      F.fprintf fmt "@[<hov 2>%a ?@ %a :@ %a@]" 
        (pp_form_lvl if_lvl) e1 (pp_form_lvl if_lvl) e2
        (pp_form_lvl if_lvl) e3 in
    maybe_paren outer if_lvl pp fmt () 
  | Fabs e -> F.fprintf fmt "`|%a|" pp_form e
(*  | Fexists of (lvar * hvar) list * form *)
  | Fforall_mem(m,e) ->
    let pp fmt () = 
      F.fprintf fmt "@[<hov 2>forall &%s,@ %a@]" 
        m (pp_form_lvl quant_lvl) e 
    in
    maybe_paren outer quant_lvl pp fmt () 
  | Fpr(f,m,args,ev) ->
    F.fprintf fmt "@[<hov 2>Pr[%a(@[%a@]) @@ &%s:@ %a]@]"
      pp_fun_name f 
      (pp_list ",@ " pp_form) args
      m
      pp_form ev
  | Frofi f -> 
    let pp fmt () = 
      F.fprintf fmt "%a%s" (pp_form_lvl proj_lvl) f "%r" in
    maybe_paren outer proj_lvl pp fmt ()

and pp_form fmt e = pp_form_lvl max_lvl fmt e

let rec pp_exp_lvl outer fmt = function
  | Epv v         -> pp_pvar fmt v
  | Etuple es     -> 
    F.fprintf fmt "(@[<hov 1>%a@])" (pp_list ",@ " pp_exp) es
  | Eproj(i,e)    -> 
    let pp fmt e = 
      F.fprintf fmt "%a.`%i" (pp_exp_lvl proj_lvl) e i in
    maybe_paren outer proj_lvl pp fmt e
  | Ecnst c       -> F.fprintf fmt "%s" c
  | Eapp(op,es)   -> 
    let pp, inner = 
      match op, es with
      | Oopp, [e] -> 
        let pp fmt () = 
          F.fprintf fmt "@[-@ %a@]" (pp_exp_lvl opp_lvl) e in
        pp, opp_lvl
      | Onot, [e] -> 
        let pp fmt () = 
          F.fprintf fmt "@[!@ %a@]" (pp_exp_lvl not_lvl) e in
        pp, not_lvl
 
      | Opow, [e1;e2] -> pp_infix pp_exp_lvl pow_lvl "^" e1 e2, pow_lvl
      | Osub, [e1;e2] -> pp_infix pp_exp_lvl add_lvl "-" e1 e2, add_lvl
      | Oadd, [e1;e2] -> pp_infix pp_exp_lvl add_lvl "+" e1 e2, add_lvl
      | Omul, [e1;e2] -> pp_infix pp_exp_lvl mul_lvl "*" e1 e2, mul_lvl
      | Odiv, [e1;e2] -> pp_infix pp_exp_lvl mul_lvl "/" e1 e2, mul_lvl
      | Oeq,  [e1;e2] -> pp_eq    pp_exp_lvl         "=" e1 e2, eq_lvl
      | Ole,  [e1;e2] -> pp_eq    pp_exp_lvl         "<=" e1 e2, eq_lvl
      | Oand, [e1;e2] -> pp_infix pp_exp_lvl mul_lvl "/\\" e1 e2, and_lvl
      | (Oopp | Opow | Oadd | Osub | Omul | Odiv | Oeq | Ole | Oand | Onot), _ -> 
        assert false
      | Ostr op, es ->
        let pp fmt () = 
          F.fprintf fmt "@[<hov 2>%s@ %a@]" op 
            (pp_list "@ " (pp_exp_lvl (app_lvl - 1))) es in
        pp, app_lvl
 
    in
    maybe_paren outer inner pp fmt ()

  | Eif(e1,e2,e3) ->
    let pp fmt () = 
      F.fprintf fmt "@[<hov 2>%a ?@ %a :@ %a@]" 
        (pp_exp_lvl if_lvl) e1 (pp_exp_lvl if_lvl) e2 (pp_exp_lvl if_lvl) e3 in
    maybe_paren outer if_lvl pp fmt () 

and pp_exp fmt e = pp_exp_lvl max_lvl fmt e

let pp_lvalue fmt lv = 
  match lv with
  | [] -> assert false
  | [v] -> pp_pvar fmt v
  | _ -> F.fprintf fmt "(@[<hov 1>%a@])" (pp_list ",@ " pp_pvar) lv


let pp_ty_distr file fmt ty = 
  match ty.ty_node with
  | BS lv -> F.fprintf fmt "%a.Dword.dword" pp_mod_name (mod_lvar file lv)
  | Bool  -> F.fprintf fmt "{0,1}"
  | G _gv -> assert false (* FIXME *)
  | Fq    -> F.fprintf fmt "FDistr.dt"
  | Prod _ -> assert false (* FIXME *)

  
let rec pp_instr file fmt = function
  | Iasgn(lv,e) ->
    F.fprintf fmt "@[<hov 2>%a =@ %a;@]" 
      pp_lvalue lv pp_exp e
  | Irnd(lv,ty,[]) ->
    F.fprintf fmt "@[<hov 2>%a =@ $%a;@]" 
      pp_lvalue lv (pp_ty_distr file) ty
  | Irnd(lv,ty,[e]) -> 
    F.fprintf fmt "@[<hov 2>%a =@ $(@[%a \\@ FSet.single %a@]);@]" 
      pp_lvalue lv (pp_ty_distr file) ty (pp_exp_lvl (app_lvl - 1)) e
  | Irnd(_lv,_ty,_l) -> 
    F.eprintf "multiple restriction not implemented@.";
    assert false
  | Icall(lv,f,e) ->
    F.fprintf fmt "@[<hov 2>%a =@ %a(%a);@]" 
      pp_lvalue lv pp_fun_name f pp_exp e
  | Iif(e,c1,c2) ->
    let pp_b2 fmt c2 = 
      if c2 <> [] then 
        F.fprintf fmt " else {@   %a@ }" (pp_block file) c2 in
    F.fprintf fmt "@[<v>if (%a) {@   %a@ }%a@]" 
      pp_exp e (pp_block file) c1 pp_b2 c2

and pp_block file fmt c = 
  F.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_instr file)) c


let pp_pvar_decl file fmt (x,ty) = 
  F.fprintf fmt "@[<hov 2>%a:@ %a@]"
    pp_pvar x (pp_type file) ty

let pp_fundef file fmt fd = 
  let pp_params fmt p = 
    F.fprintf fmt "@[<hov 2>%a@]" 
      (pp_list ",@ " (pp_pvar_decl file)) p in 
  let pp_rettyp fmt = function
    | None -> F.fprintf fmt "unit"
    | Some(_,ty) -> pp_type file fmt ty in
  let pp_vard fmt d = 
    F.fprintf fmt "var %a;" (pp_pvar_decl file) d in
  let pp_local fmt loc = 
    if loc <> [] then
      F.fprintf fmt "%a@ " (pp_list "@ " pp_vard) loc in
  let pp_ret fmt = function
    | None -> ()
    | Some(v,_) -> F.fprintf fmt "return %a;" pp_pvar v in
  F.fprintf fmt "@[<v>proc %s(%a) : %a = {@   @[<v>%a%a@ %a@]@ }@]"
    fd.f_name
    pp_params fd.f_param
    pp_rettyp fd.f_res
    pp_local fd.f_local
    (pp_block file) fd.f_body
    pp_ret fd.f_res
  
let pp_mod_param fmt (name,ty) = 
  F.fprintf fmt "%s:%s" name ty

let pp_mod_params fmt = function
  | [] -> ()
  | l -> 
    F.fprintf fmt "(@[<hov 2>%a@])"
      (pp_list ",@ " pp_mod_param) l

let rec pp_mod_body file fmt = function
  | Mod_def mc ->
    let isMCvar = function MCvar _ -> true | _ -> false in
    let vars, other = List.partition isMCvar mc in
    (* We try to merge the declaration of global variables *)
    let ht = Hty.create 7 in
    let add = function
      | MCvar (x,ty) -> 
        let l = try Hty.find ht ty with Not_found -> [] in
        Hty.replace ht ty (x::l)
      | _ -> assert false in
    List.iter add vars;
    let vars = Hty.fold (fun ty l vars -> (l,ty) :: vars) ht [] in
    let pp_var fmt (l,ty) = 
      F.fprintf fmt "@[<hov 2>var %a: %a@]"
        (pp_list ",@ " pp_pvar) l (pp_type file) ty in
    let pp_vars fmt vars = 
      if vars <> [] then
        F.fprintf fmt "%a@ @ " (pp_list "@ " pp_var) vars in
    F.fprintf fmt "{@   @[<v>%a%a@]@ }"
      pp_vars vars (pp_list "@ @ " (pp_mod_comp file)) other
  | Mod_alias mn -> pp_mod_name fmt mn

and pp_mod_comp file fmt = function
  | MCmod md -> pp_mod_def file fmt md
  | MCfun fd -> pp_fundef file fmt fd
  | MCvar (v,ty) -> F.fprintf fmt "var %a" (pp_pvar_decl file) (v,ty)

and pp_mod_def ?(local=false) file fmt md = 
  F.fprintf fmt "@[<v>%smodule %s%a = %a@]"
    (if local then "local " else "")
    md.mod_name pp_mod_params md.mod_param (pp_mod_body file) md.mod_body

let pp_lvars_mod fmt lvars = 
  if Lenvar.H.length lvars <> 0 then 
    let out _ {tvar_mod = name} = 
      F.fprintf fmt "clone import AWord as %s.@ " name
    in
    F.fprintf fmt "(** { Bitstring declarations. } *)@ @ ";
    F.fprintf fmt "require AWord.@ @ ";
    Lenvar.H.iter out lvars;
    F.fprintf fmt "@ "

let pp_gvars_mod fmt gvars = 
  if Groupvar.H.length gvars <> 0 then 
    let out _ {tvar_mod = name} = 
      F.fprintf fmt "clone import CyclicGroup.CG as %s.@ " name
    in
    F.fprintf fmt "(** { Group declarations. } *)@ @ ";
    F.fprintf fmt "require import PrimeField.@ ";
    F.fprintf fmt "require import SDField.@ ";
    F.fprintf fmt "import FSet.Dexcepted.@ ";
    F.fprintf fmt "import F.@ ";
    F.fprintf fmt "require CyclicGroup.@ @ ";
    Groupvar.H.iter out gvars;
    F.fprintf fmt "@ "

(** {3 Bilinear map } *)

let pp_bilinear_mod file fmt bvars = 
  if Esym.H.length bvars <> 0 then
    let out bv s = 
      let g1 = gvar_mod file bv.Esym.source1 in
      let g2 = gvar_mod file bv.Esym.source2 in
      let gt = gvar_mod file bv.Esym.target in
      let pp_with g wg =
         F.fprintf fmt "     type %s.group <- %s.group,@ " g wg;
         F.fprintf fmt "     op   %s.( * ) <- %s.( * ),@ " g wg;
         F.fprintf fmt "     op   %s.([-]) <- %s.([-]),@ " g wg;
         F.fprintf fmt "     op   %s.( / ) <- %s.( / ),@ " g wg;
         F.fprintf fmt "     op   %s.( ^ ) <- %s.( ^ ),@ " g wg;
         F.fprintf fmt "     op   %s.log   <- %s.log"      g wg in
      F.fprintf fmt "clone Bilinear.Bl as %s with@ " s;
      pp_with "G1" g1;
      F.fprintf fmt ",@ ";
      pp_with "G2" g2;
      F.fprintf fmt ",@ ";
      pp_with "GT" gt;
      F.fprintf fmt ".@ @ " in

    F.fprintf fmt "(** { Bilinear Map declarations. } *)@ @ ";
    F.fprintf fmt "require Bilinear.@ @ ";
    Esym.H.iter out bvars;
    F.fprintf fmt "@ "

let pp_hash_mod fmt file = 
  if Hsym.H.length file.hvar <> 0 then 
    let out h info =
      match info.h_kind with
      | Hop oinfo ->
        F.fprintf fmt "@[<hov 2>op %s :@ %a ->@ %a.@]@ "
          oinfo.o_name (pp_type file) h.Hsym.dom (pp_type file) h.Hsym.codom in
    F.fprintf fmt "(** { operators declarations. } *)@ @ ";
    Hsym.H.iter out file.hvar;
    F.fprintf fmt "@ "
  



let pp_var_decl file fmt x = 
  F.fprintf fmt "%a:%a"
    Vsym.pp x (pp_type file) (x.Vsym.ty)

let pp_assumption fmt file _name assum =
  (* Declare the module type for the adversary *)
  let pp_adv_decl file fmt pub = 
    F.fprintf fmt "proc main (@[%a@]) : bool"
      (pp_list ",@ " (pp_var_decl file)) pub in
  let pp_mod_ty fmt pub = 
    F.fprintf fmt "module type %s = {@   %a@ }.@ "
      assum.a_advty (pp_adv_decl file) pub in
    
  F.fprintf fmt "@[<v>%a@ %a.@ @ %a.@]@ @ "
    pp_mod_ty assum.a_param
    (pp_mod_def file) assum.a_cmd1
    (pp_mod_def file) assum.a_cmd2

    
let pp_assumptions fmt file = 
  if Ht.length file.assump <> 0 then begin
    F.fprintf fmt "(** { Assumptions. } *)@ @ ";
    Ht.iter (pp_assumption fmt file) file.assump
  end

let pp_oname1 fmt name = F.fprintf fmt "o%a" Osym.pp name
let pp_oname fmt name = F.fprintf fmt "O.%a" pp_oname1 name

let obinding tbl = 
  Osym.H.fold (fun k v l -> (k,v)::l) tbl [] 

let abinding tbl = 
  Asym.H.fold (fun k v l -> (k,v)::l) tbl [] 

let pp_adv_type fmt file = 
  let pp_orcl_decl fmt (oname, oinfo) = 
    F.fprintf fmt "@[proc %a (@[%a@]) :@ %a@]"
      pp_oname1 oname 
      (pp_list ",@ " (pp_var_decl file)) oinfo.oparams
      (pp_type file) oinfo.ores.e_ty in
  let pp_orcl_ty fmt oinfo = 
    F.fprintf fmt "@[<v>module type Orcl = {@   @[<v>%a@]@ }.@]@ " 
      (pp_list "@ " pp_orcl_decl) (List.rev (obinding oinfo)) in
  let pp_adv_decl fmt (name,os) =
    F.fprintf fmt "@[proc a%a (_ : %a) : %a {%a}@]"
      Asym.pp name (pp_type file) name.Asym.dom (pp_type file) name.Asym.codom
      (pp_list ",@ " pp_oname) os in
  let pp_adv_ty fmt ainfo = 
    F.fprintf fmt "@[<v>module type Adv (O:Orcl) = {@    @[<v>%a@]@ }.@]@ "
      (pp_list "@ " pp_adv_decl) (List.rev (abinding ainfo))
  in
  let ginfo = (adv_info file).adv_g in
  F.fprintf fmt "@[<v>%a@ %a@ @]"
    pp_orcl_ty ginfo.oinfo
    pp_adv_ty  ginfo.ainfo

let pp_cmd local file fmt = function
  | Cmod md -> 
    F.fprintf fmt "%a." (pp_mod_def ~local file) md
  | Clemma(loc,name,f,Some proof) ->
    F.fprintf fmt "%slemma %s:@   @[%a@]."
      (if loc then "local " else "") name pp_form f;
    F.fprintf fmt "@ proof.@   @[<v>%a@]@ qed." proof ()
      
  | Clemma(loc,name,f,None) ->
    assert (loc = false);
    F.fprintf fmt "@[<v>axiom %s:@   @[%a@]." name pp_form f 

let pp_cmds local file fmt cmd = 
  pp_list "@ @ " (pp_cmd local file) fmt cmd
      
let pp_adv_decl fmt file = 
  let r = [] in
  (*  Hsym.H.fold (fun _ info r -> (info.h_th^"."^info.h_mod)::r)
      file.hvar [] in *)
  let add_mod r = function
    | Cmod md -> md.mod_name :: r
    | _ -> r in
  let r = List.fold_left add_mod r file.glob_decl in      
  let r = 
    if Groupvar.H.length file.grvar <> 0 then "SDF.SD1query.SDN.Count" :: r 
    else r in
  let name,ty = adv_decl file in
  F.fprintf fmt "declare module %s : %s {@[<hov 2>%a@]}.@ @ "
    name ty (pp_list ", " F.pp_print_string) r 

let pp_file fmt file = 
  F.fprintf fmt "@[<v>require import Real.@ ";
  F.fprintf fmt "require import ZooUtil.@ ";
  pp_lvars_mod fmt file.levar;
  pp_gvars_mod fmt file.grvar;
  pp_bilinear_mod file fmt file.bvar;
  pp_hash_mod fmt file;
  pp_assumptions fmt file;
  pp_adv_type fmt file;
  pp_cmds false file fmt (List.rev file.glob_decl);
  F.fprintf fmt "@ @ section.@ @   @[<v>%a%a@]@ @ end section."
    pp_adv_decl file
    (pp_cmds true file) (List.rev file.loca_decl);

  
  F.fprintf fmt "@]@."
  
    




  
