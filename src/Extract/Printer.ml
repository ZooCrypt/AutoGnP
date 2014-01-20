open Util
open Type
open Expr
open File

let pp_pvar fmt (ms,s) =
  if ms = [] then Format.fprintf fmt "%s" s
  else Format.fprintf fmt "%a.%s" (pp_list "." Format.pp_print_string) ms s

let pp_mem fmt s = Format.fprintf fmt "&%s" s

let rec pp_mod_name fmt mn = 
  if mn.ma = [] then Format.fprintf fmt "%s" mn.mn
  else 
    Format.fprintf fmt "%s(@[<hov 1>%a@])" 
      mn.mn (pp_list ",@ " pp_mod_name) mn.ma

let pp_fun_name fmt (mn,s) = 
  Format.fprintf fmt "%a.%s" pp_mod_name mn s

let pp_tvar fmt i = 
  let m =  {mn = i.tvar_mod; ma = []} in
  Format.fprintf fmt "%a.%s" pp_mod_name m i.tvar_ty

let rec pp_type file fmt ty = 
 match ty.ty_node with
  | BS lv    -> pp_tvar fmt (get_lvar file lv)
  | Bool     -> Format.fprintf fmt "bool"
  | G gv     -> pp_tvar fmt (get_gvar file gv)
  | Fq       -> Format.fprintf fmt "F.t"
  | Prod tys -> 
    Format.fprintf fmt "(@[%a@])" (pp_list " *@ " (pp_type file)) tys

let pp_at_mem fmt = function
  | None -> ()
  | Some m -> Format.fprintf fmt "{%s}" m

let rec pp_form fmt = function
  | Fv (v, m)   -> Format.fprintf fmt "%a%a" pp_pvar v pp_at_mem m 
  | Ftuple es     ->
    Format.fprintf fmt "(@[<hov 1>%a@])" (pp_list ",@ " pp_form) es
  | Fproj (i,e)   -> Format.fprintf fmt "%a.`%i" pp_form e i
  | Fcnst c       -> Format.fprintf fmt "%s" c
  | Fapp(op,[])   -> Format.fprintf fmt "%s" op
  | Fapp(op,es)   -> 
    Format.fprintf fmt "(@[<hov 2>%s@ %a@])" op (pp_list "@ " pp_form) es
  | Fif(e1,e2,e3) ->
    Format.fprintf fmt "(@[<hov 2>if %a then@ %a else@ %a@])" 
      pp_form e1 pp_form e2 pp_form e3
  | Feq(e1,e2) ->
    Format.fprintf fmt "(@[<hov 2>%a =@ %a@])" pp_form e1 pp_form e2
  | Fle(e1,e2) ->
    Format.fprintf fmt "(@[<hov 2>%a <=@ %a@])" pp_form e1 pp_form e2
  | Fabs e -> Format.fprintf fmt "`|%a|" pp_form e
(*  | Fexists of (lvar * hvar) list * form *)
  | Fforall_mem(m,e) ->
    Format.fprintf fmt "(@[<hov 2>forall &%s,@ %a@])" m pp_form e 
  | Fpr(f,m,args,ev) ->
    Format.fprintf fmt "@[<hov 2>Pr[%a(@[%a@]) @@ &%s:@ %a]@]"
      pp_fun_name f 
      (pp_list ",@ " pp_form) args
      m
      pp_form ev

let rec pp_exp fmt = function
  | Epv v         -> pp_pvar fmt v
  | Etuple es     -> 
    Format.fprintf fmt "(@[<hov 1>%a@])" (pp_list ",@ " pp_exp) es
  | Eproj(i,e)    -> Format.fprintf fmt "%a.`%i" pp_exp e i
  | Ecnst c       -> Format.fprintf fmt "%s" c
  | Eapp(op,es)   -> 
    Format.fprintf fmt "(@[<hov 2>%s@ %a@])" op (pp_list "@ " pp_exp) es
  | Eif(e1,e2,e3) ->
    Format.fprintf fmt "(@[<hov 2>%a ?@ %a :@ %a@])" 
      pp_exp e1 pp_exp e2 pp_exp e3
  | Eeq(e1, e2)   ->
    Format.fprintf fmt "(@[<hov 2>%a =@ %a@])" pp_exp e1 pp_exp e2

let pp_lvalue fmt lv = 
  match lv with
  | [] -> assert false
  | [v] -> pp_pvar fmt v
  | _ -> Format.fprintf fmt "(@[<hov 1>%a@])" (pp_list ",@ " pp_pvar) lv


let pp_ty_distr file fmt ty = 
  match ty.ty_node with
  | BS lv -> Format.fprintf fmt "%a.Dword.dword" pp_mod_name (mod_lvar file lv)
  | Bool  -> Format.fprintf fmt "{0,1}"
  | G _gv -> assert false (* FIXME *)
  | Fq    -> Format.fprintf fmt "FDistr.dt"
  | Prod _ -> assert false (* FIXME *)

  
let rec pp_instr file fmt = function
  | Iasgn(lv,e) ->
    Format.fprintf fmt "@[<hov 2>%a =@ %a;@]" 
      pp_lvalue lv pp_exp e
  | Irnd(lv,ty) ->
    Format.fprintf fmt "@[<hov 2>%a =@ $%a;@]" 
      pp_lvalue lv (pp_ty_distr file) ty
  | Icall(lv,f,e) ->
    Format.fprintf fmt "@[<hov 2>%a =@ %a(%a);@]" 
      pp_lvalue lv pp_fun_name f pp_exp e
  | Iif(e,c1,c2) ->
    let pp_b2 fmt c2 = 
      if c2 <> [] then 
        Format.fprintf fmt " else {@   %a@ }" (pp_block file) c2 in
    Format.fprintf fmt "@[<v>if (%a) {@   %a@ }%a@]" 
      pp_exp e (pp_block file) c1 pp_b2 c2

and pp_block file fmt c = 
  Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_instr file)) c


let pp_pvar_decl file fmt (x,ty) = 
  Format.fprintf fmt "@[<hov 2>%a:@ %a@]"
    pp_pvar x (pp_type file) ty

let pp_fundef file fmt fd = 
  let pp_params fmt p = 
    Format.fprintf fmt "@[<hov 2>%a@]" 
      (pp_list ",@ " (pp_pvar_decl file)) p in 
  let pp_rettyp fmt = function
    | None -> Format.fprintf fmt "unit"
    | Some(_,ty) -> pp_type file fmt ty in
  let pp_vard fmt d = 
    Format.fprintf fmt "var %a;" (pp_pvar_decl file) d in
  let pp_local fmt loc = 
    if loc <> [] then
      Format.fprintf fmt "%a@ " (pp_list "@ " pp_vard) loc in
  let pp_ret fmt = function
    | None -> ()
    | Some(v,_) -> Format.fprintf fmt "return %a;" pp_pvar v in
  Format.fprintf fmt "@[<v>proc %s(%a) : %a = {@   @[<v>%a%a@ %a@]@ }@]"
    fd.f_name
    pp_params fd.f_param
    pp_rettyp fd.f_res
    pp_local fd.f_local
    (pp_block file) fd.f_body
    pp_ret fd.f_res
  
let pp_mod_param fmt (name,ty) = 
  Format.fprintf fmt "%s:%s" name ty

let pp_mod_params fmt = function
  | [] -> ()
  | l -> 
    Format.fprintf fmt "(@[<hov 2>%a@])"
      (pp_list ",@ " pp_mod_param) l

let rec pp_mod_body file fmt = function
  | Mod_def mc ->
    let isMCvar = function MCvar _ -> true | _ -> false in
    let vars, other = List.partition isMCvar mc in
    let pp_vars fmt vars = 
      if vars <> [] then
        Format.fprintf fmt "%a@ @ " (pp_list "@ " (pp_mod_comp file)) vars in
    Format.fprintf fmt "{@   @[<v>%a%a@]@ }"
      pp_vars vars (pp_list "@ @ " (pp_mod_comp file)) other
  | Mod_alias mn -> pp_mod_name fmt mn

and pp_mod_comp file fmt = function
  | MCmod md -> pp_mod_def file fmt md
  | MCfun fd -> pp_fundef file fmt fd
  | MCvar (v,ty) -> Format.fprintf fmt "var %a" (pp_pvar_decl file) (v,ty)

and pp_mod_def ?(local=false) file fmt md = 
  Format.fprintf fmt "@[<v>%smodule %s%a = %a@]"
    (if local then "local " else "")
    md.mod_name pp_mod_params md.mod_param (pp_mod_body file) md.mod_body

let pp_lvars_mod fmt lvars = 
  if Lenvar.H.length lvars <> 0 then 
    let out _ {tvar_mod = name} = 
      Format.fprintf fmt "clone AWord as %s.@ " name
    in
    Format.fprintf fmt "(** { Bitstring declarations. } *)@ @ ";
    Format.fprintf fmt "require AWord.@ @ ";
    Lenvar.H.iter out lvars;
    Format.fprintf fmt "@ "

let pp_gvars_mod fmt gvars = 
  if Groupvar.H.length gvars <> 0 then 
    let out _ {tvar_mod = name} = 
      Format.fprintf fmt "clone CyclicGroup.CG as %s.@ " name
    in
    Format.fprintf fmt "(** { Group declarations. } *)@ @ ";
    Format.fprintf fmt "require import PrimeField.@ ";
    Format.fprintf fmt "require CyclicGroup.@ @ ";
    Groupvar.H.iter out gvars;
    Format.fprintf fmt "@ "

let pp_hash_mod fmt file = 
  if Hsym.H.length file.hvar <> 0 then 
    let out_t name fmt t = 
      Format.fprintf fmt "type %s <- @[%a@]" name (pp_type file) t in
    let out h info = 
      Format.fprintf fmt "@[<v>clone HashOp as %s with@  @[<v>%a,@ %a.@]@]@ "
        info.h_th (out_t "from") h.Hsym.dom (out_t "to") h.Hsym.codom in
    Format.fprintf fmt "(** { Hash declarations. } *)@ @ ";
    Format.fprintf fmt "require HashOp.@ @ ";
    Hsym.H.iter out file.hvar;
    Format.fprintf fmt "@ "

let pp_var_decl file fmt x = 
  Format.fprintf fmt "%a:%a"
    Vsym.pp x (pp_type file) (x.Vsym.ty)

let pp_assumption fmt file _name assum =
  (* Declare the module type for the adversary *)
  let pp_adv_decl file fmt pub = 
    Format.fprintf fmt "proc main (@[%a@]) : bool"
      (pp_list ",@ " (pp_var_decl file)) pub in
  let pp_mod_ty fmt pub = 
    Format.fprintf fmt "module type %s = {@   %a@ }.@ "
      assum.a_advty (pp_adv_decl file) pub in
    
  Format.fprintf fmt "@[<v>%a@ %a.@ @ %a.@]@ @ "
    pp_mod_ty assum.a_param
    (pp_mod_def file) assum.a_cmd1
    (pp_mod_def file) assum.a_cmd2

    
let pp_assumptions fmt file = 
  if Ht.length file.assump <> 0 then begin
    Format.fprintf fmt "(** { Assumptions. } *)@ @ ";
    Ht.iter (pp_assumption fmt file) file.assump
  end

let pp_oname fmt name = Format.fprintf fmt "O.o%a" Osym.pp name

let obinding tbl = 
  Osym.H.fold (fun k v l -> (k,v)::l) tbl [] 

let abinding tbl = 
  Asym.H.fold (fun k v l -> (k,v)::l) tbl [] 

let pp_adv_type fmt file = 
  let pp_orcl_decl fmt (oname, oinfo) = 
    Format.fprintf fmt "@[proc %a (@[%a@]) :@ %a@]"
      pp_oname oname 
      (pp_list ",@ " (pp_var_decl file)) oinfo.oparams
      (pp_type file) oinfo.ores.e_ty in
  let pp_orcl_ty fmt oinfo = 
    Format.fprintf fmt "@[<v>module type Orcl = {@   @[<v>%a@]@ }.@]@ " 
      (pp_list "@ " pp_orcl_decl) (obinding oinfo) in
  let pp_adv_decl fmt (name,os) =
    Format.fprintf fmt "@[proc a%a (_ : %a) : %a {%a}@]"
      Asym.pp name (pp_type file) name.Asym.dom (pp_type file) name.Asym.codom
      (pp_list ",@ " pp_oname) os in
  let pp_adv_ty fmt ainfo = 
    Format.fprintf fmt "@[<v>module type Adv (O:Orcl) = {@    @[<v>%a@]@ }.@]@ "
      (pp_list "@ " pp_adv_decl) (abinding ainfo)
  in
  let ginfo = (adv_info file).adv_g in
  Format.fprintf fmt "@[<v>%a@ %a@ @]"
    pp_orcl_ty ginfo.oinfo
    pp_adv_ty  ginfo.ainfo

let pp_cmd local file fmt = function
  | Cmod md -> 
    Format.fprintf fmt "%a." (pp_mod_def ~local file) md
  | Clemma(loc,name,f,Some proof) ->
    Format.fprintf fmt "%slemma %s:@   @[%a@]."
      (if loc then "local " else "") name pp_form f;
    Format.fprintf fmt "@ proof.@   %a@ qed." proof ()
      
  | Clemma(loc,name,f,None) ->
    assert (loc = false);
    Format.fprintf fmt "@[<v>axiom %s:@   @[%a@]." name pp_form f 

let pp_cmds local file fmt cmd = 
  pp_list "@ @ " (pp_cmd local file) fmt cmd
      
let pp_adv_decl fmt file = 
  let r = 
    Hsym.H.fold (fun _ info r -> (info.h_th^"."^info.h_mod)::r)
      file.hvar [] in
  let add_mod r = function
    | Cmod md -> md.mod_name :: r
    | _ -> r in
  let r = List.fold_left add_mod r file.glob_decl in      
  let name,ty = adv_decl file in
  Format.fprintf fmt "declare module %s : %s {@[<hov 2>%a@]}.@ @ "
    name ty (pp_list ", " Format.pp_print_string) r 

let pp_file fmt file = 
  Format.fprintf fmt "@[<v>require import Real.@ ";
  Format.fprintf fmt "require import ZooUtil.@ ";
  pp_lvars_mod fmt file.levar;
  pp_gvars_mod fmt file.grvar;
  pp_hash_mod fmt file;
  pp_assumptions fmt file;
  pp_adv_type fmt file;
  pp_cmds false file fmt (List.rev file.glob_decl);
  Format.fprintf fmt "@ @ section.@ @   @[<v>%a%a@]@ @ end section."
    pp_adv_decl file
    (pp_cmds true file) (List.rev file.loca_decl);

  
  Format.fprintf fmt "@]@."
  
    




  
