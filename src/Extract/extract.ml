open Util
open Type
open Expr 
open Game 
open Assumption
open TheoryState
open CoreRules

module Ht = Hashtbl

(** { 1 Bitstring type variables} *)
let pp_lvar_mod fmt lv = 
  Format.fprintf fmt "BS_%a" Lenvar.pp lv

let pp_lvar_ty fmt lv = 
  Format.fprintf fmt "%a.bitstring" pp_lvar_mod lv 

let pp_lvars fmt lvars = 
  if Ht.length lvars <> 0 then 
    let out _ lv = 
      Format.fprintf fmt "clone AWord as %a.@ " pp_lvar_mod lv
    in
    Format.fprintf fmt "(** { Bitstring declarations. } *)@ @ ";
    Format.fprintf fmt "require AWord.@ @ ";
    Ht.iter out lvars;
    Format.fprintf fmt "@ "

(** { 2 Group type variables} *)
let pp_gvar_mod fmt gv = 
  Format.fprintf fmt "G%a" Groupvar.pp gv

let pp_gvar_ty fmt gv = 
  Format.fprintf fmt "%a.group" pp_gvar_mod gv

let pp_gvars fmt gvars = 
  if Ht.length gvars <> 0 then
    let out _ gv =
      Format.fprintf fmt "clone CyclicGroup.CG as %a.@ " pp_gvar_mod gv in
    Format.fprintf fmt "(** { Group declarations. } *)@ @ ";
    Format.fprintf fmt "require import PrimeField.@ ";
    Format.fprintf fmt "require CyclicGroup.@ @ ";
    Ht.iter out gvars;
    Format.fprintf fmt "@ "

(** {3 Bilinear map } *)

let pp_bilinear _fmt _bvars = ()

(** { 4 Type } *)
let rec pp_type fmt ty = 
  match ty.ty_node with
  | BS lv -> pp_lvar_ty fmt lv
  | Bool  -> Format.fprintf fmt "bool"
  | G gv  -> pp_gvar_ty fmt gv
  | Fq    -> Format.fprintf fmt "F.t"
  | Prod tys -> 
    Format.fprintf fmt "(@[%a@])" 
      (pp_list " *@ " pp_type) tys

(** { 5 Variables } *)

let pp_var = Vsym.pp

let pp_var_decl fmt v = 
  Format.fprintf fmt "%a:@ %a"
    pp_var v pp_type v.Vsym.ty

let pp_var_decls fmt vs = 
  Format.fprintf fmt "%a" (pp_list ",@ " pp_var_decl) vs 

let pp_pvar_decl fmt e =
  Format.fprintf fmt "@[var %a@]" pp_var_decl (destr_V e)

let pp_pvar_decls fmt vs =
  Format.fprintf fmt "@[<v>%a@]"
  (pp_list "@ " pp_pvar_decl) (Se.elements vs)

let pp_lpvar_decls fmt vs =
  Format.fprintf fmt "@[<v>%a@]"
  (pp_list ";@ " pp_pvar_decl) (Se.elements vs)

let pp_tuple_var fmt vs = 
  Format.fprintf fmt "(@[%a@])" (pp_list ",@ " pp_var) vs
(** { 6 Expression } *)

let pp_cnst fmt ty = function
  | GGen -> 
    Format.fprintf fmt "%a.g" pp_gvar_mod (destr_G ty)
  | FNat i -> Format.fprintf fmt "(F.ofint %i)" i
  | Z -> Format.fprintf fmt "%a.zeros" pp_lvar_mod (destr_BS ty)
  | B b -> Format.fprintf fmt "%b" b

let string_of_nop ty = function
  | FPlus -> "F.(+)"
  | FMult -> "F.( * )"
  | Xor   -> 
    begin match ty.ty_node with 
    | BS lv -> Util.fsprintf "%a.(^)" pp_lvar_mod lv |> Util.fsget
    | Bool  -> assert false
    | _     -> assert false
    end
  | Land -> "(/\\)" 
  | GMult -> Util.fsprintf "%a.( * )" pp_gvar_mod (destr_G ty) |> Util.fsget
  
let rec pp_exp fmt e = 
  match e.e_node with
  | V x         -> pp_var fmt x
  | H(_h,_e)      -> assert false
  | Tuple es    -> Format.fprintf fmt "(@[%a@])" (pp_list ",@ " pp_exp) es
  | Proj(i,e)   -> Format.fprintf fmt "%a.`%i" pp_exp e i
  | Cnst c      -> pp_cnst fmt e.e_ty c
  | App(op,es)  -> pp_op fmt op es
  | Nary(op,es) -> pp_nop fmt op es 
  | Exists _    -> assert false

and pp_op fmt op es = 
  match op, es with
  | GExp _, [e1;e2] ->
    Format.fprintf fmt "(@[<hov 2>%a.(^)@ %a@ %a@])"
      pp_gvar_mod (destr_G e1.e_ty) pp_exp e1 pp_exp e2
  | GLog lv,[e] ->
    Format.fprintf fmt "(@[<hov 2>%a.log@ %a@])"
      pp_gvar_mod lv pp_exp e
  | FOpp, [e]->
    Format.fprintf fmt "(@[<hov 2>F.[-]@ %a@])" pp_exp e
  | FMinus, [e1;e2] ->
    Format.fprintf fmt "(@[<hov 2>F.(-)@ %a %a@])" pp_exp e1 pp_exp e2
  | FInv, [e] -> 
    Format.fprintf fmt "(@[<hov 2>F.inv@ %a@])" pp_exp e
  | FDiv, [e1;e2] ->
    Format.fprintf fmt "(@[<hov 2>F.(/)@ %a %a@])" pp_exp e1 pp_exp e2
  | Eq, [e1;e2] ->
    Format.fprintf fmt "(@[<hov 2> %a =@ %a@])" pp_exp e1 pp_exp e2
  | Not, [e] ->
    Format.fprintf fmt "(@[<hov 2>!@ %a@])" pp_exp e
  | Ifte, [e1;e2;e3] -> 
    Format.fprintf fmt "(@[<hov 2>%a ?@ %a :@ %a@])" 
    pp_exp e1 pp_exp e2 pp_exp e3
  | EMap _, _ -> assert false 
  | _, _ -> assert false

and pp_nop fmt op es = 
  let sop = string_of_nop (List.hd es).e_ty op in
  let rec aux fmt es =
    match es with
    | [] -> assert false
    | [e] -> pp_exp fmt e
    | e::es -> Format.fprintf fmt "(%s@ %a@ %a)" sop pp_exp e aux es in
  Format.fprintf fmt "@[<hov 2>%a@]" aux es

(** { 7 Instruction } *)

let pp_ty_distr fmt ty =
  match ty.ty_node with
  | BS lv -> Format.fprintf fmt "%a.Dword.dword" pp_lvar_mod lv
  | Bool  -> Format.fprintf fmt "{0,1}"
  | G _gv -> assert false (* FIXME *)
  | Fq    -> Format.fprintf fmt "FDistr.dt"
  | Prod _ -> assert false (* FIXME *)
  
let pp_distr fmt (ty,l) = 
  assert (l = []); (* FIXME *)
  pp_ty_distr fmt ty

let pp_adv_name aname fmt faname = 
  Format.fprintf fmt "%s.a%a" aname Asym.pp faname

let pp_gcmd aname fmt = function
  | GLet(x,e) -> 
    Format.fprintf fmt "@[<hov 2>%a =@ %a;@]" pp_var x pp_exp e
  | GSamp(x,d) ->
    Format.fprintf fmt "@[<hov 2>%a =@ $%a;@]" pp_var x pp_distr d
  | GCall(xs,a,e,_) ->
    Format.fprintf fmt "@[<hov 2>%a =@ %a(%a);@]" 
      pp_tuple_var xs (pp_adv_name aname) a pp_exp e

let pp_gcmds aname fmt cmds = 
  Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_gcmd aname)) cmds

let pp_gcmdsA = pp_gcmds "A"

(** { 8 Assumption } *)

let pp_assump name fmt i = 
  Format.fprintf fmt "G%s%i" name i

let pp_assumption1 fmt name assum =
  (* Declare the module type for the adversary *)
  let pp_adv_decl fmt pub = 
    Format.fprintf fmt "proc main (@[%a@]) : bool"
      (pp_list ",@ " pp_var_decl) (Vsym.S.elements pub) in
  let pp_mod_ty fmt pub = 
    Format.fprintf fmt "module type Adv_%s = {@   %a@ }.@ "
      name pp_adv_decl pub in
    
  (* Declare the module for G1 and G2 *)
  let pp_body pub fmt gcmds : unit= 
    Format.fprintf fmt "@[<v>%a@ b:bool;@ %a@ b = A.main%a;@ return b;@]"
      pp_lpvar_decls (gdef_vars gcmds) 
      pp_gcmdsA gcmds
      pp_tuple_var (Vsym.S.elements pub)
  in
  let pp_mod i pub fmt gcmds : unit = 
    Format.fprintf fmt "@[<v>module %a (A:Adv_%s) = {@ "
      (pp_assump name) i name;
    Format.fprintf fmt "  @[<v>proc main () : bool = {@   %a@ }@]@ }.@]@ "
      (pp_body pub) gcmds in

  Format.fprintf fmt "@[<v>%a@ %a@ %a@]@ "
    pp_mod_ty assum.ad_pubvars
    (pp_mod 1 assum.ad_pubvars) assum.ad_prefix1
    (pp_mod 2 assum.ad_pubvars) assum.ad_prefix2 
    
let pp_assumption fmt assum = 
  if Ht.length assum <> 0 then begin
    Format.fprintf fmt "(** { Assumptions. } *)@ @ ";
    Ht.iter (pp_assumption1 fmt) assum
  end

type orcl_info = { 
  oparams : Vsym.t list;
  obody   : lcmd list;
  ores    : expr;
} 

type adv_info = Osym.t list

type game_info = {
  oinfo : orcl_info Osym.H.t;
  ainfo : adv_info  Asym.H.t;
}

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
    


let obinding tbl = 
  Osym.H.fold (fun k v l -> (k,v)::l) tbl [] 

let abinding tbl = 
  Asym.H.fold (fun k v l -> (k,v)::l) tbl [] 

let pp_oname fmt name = Format.fprintf fmt "O.o%a" Osym.pp name

let pp_adv_decl fmt ginfo =
  let pp_orcl_decl fmt (oname, oinfo) = 
    Format.fprintf fmt "@[proc %a (%a) :@ %a@]"
      pp_oname oname 
      pp_var_decls oinfo.oparams
      pp_type oinfo.ores.e_ty in
  let pp_orcl_ty fmt oinfo = 
    Format.fprintf fmt "@[<v>module type Orcl = {@   @[<v>%a@]@ }.@]@ " 
      (pp_list "@ " pp_orcl_decl) (obinding oinfo) in
  let pp_adv_decl fmt (name,os) =
    Format.fprintf fmt "@[proc a%a (_ : %a) : %a {%a}@]"
      Asym.pp name pp_type name.Asym.dom pp_type name.Asym.codom
      (pp_list ",@ " pp_oname) os in
  let pp_adv_ty fmt ainfo = 
    Format.fprintf fmt "@[<v>module type Adv (O:Orcl) = {@    @[<v>%a@]@ }.@]@ "
      (pp_list "@ " pp_adv_decl) (abinding ainfo)
  in
  Format.fprintf fmt "@[<v>%a@ %a@ @]"
    pp_orcl_ty ginfo.oinfo
    pp_adv_ty  ginfo.ainfo


let pp_game name fmt ju = 
  let ginfo = game_info ju.ju_gdef in
  let pp_orcl_def _fmt _ = assert false (* FIXME *) in
  let pp_orcl_mod fmt oinfo = 
    Format.fprintf fmt "@[<v>module O = {@   @[<v>%a@]@ }@]"
      (pp_list "@ " pp_orcl_def) (obinding oinfo) in
  let pp_adv_mod fmt _ainfo = Format.fprintf fmt "module A = A(O)" in
  let pp_main fmt cs =
    Format.fprintf fmt "@[<v>proc main() : unit = {@   %a@ }@]"
      pp_gcmdsA cs in
  Format.fprintf fmt 
    "@[<v>module %s (A:Adv) = {@   @[<v>%a@ @ %a@ @ %a@ @ %a@]@ }.@ @ @]"
    name 
    pp_pvar_decls (ju_vars ju)
    pp_orcl_mod ginfo.oinfo
    pp_adv_mod  ginfo.ainfo
    pp_main     ju.ju_gdef

type bound = 
  | Bint of int
  | Bhalf
  | Bf
  | Bbs of IdType.internal Lenvar.gid
  | Bju of (string * judgment)
  | Badd of bound * bound
  | Bsub of bound * bound
  | Bmul of bound * bound

let pp_prob fmt (name,ju) = 
  Format.fprintf fmt "@[Pr[%s(A).main() @ &m :@ %a]@]" name pp_exp ju.ju_ev

let rec pp_bound fmt bound = 
  match bound with
  | Bint n -> Format.fprintf fmt "%i%%r" n
  | Bhalf  -> Format.fprintf fmt "1%%r/2%%r" 
  | Bf     -> Format.fprintf fmt "1%%r/F.q%%r"
  | Bbs lv -> Format.fprintf fmt "1%%r/(2^%a.length)%%r" pp_lvar_mod lv
  | Bju ju -> pp_prob fmt ju 
  | Badd(b1,b2) -> Format.fprintf fmt "(%a + %a)" pp_bound b1 pp_bound b2
  | Bsub(b1,b2) -> Format.fprintf fmt "(%a - %a)" pp_bound b1 pp_bound b2
  | Bmul(b1,b2) -> Format.fprintf fmt "(%a * %a)" pp_bound b1 pp_bound b2

type cmp = Eq | Le

let pp_cmp fmt = function
  | Eq -> Format.fprintf fmt "="
  | Le -> Format.fprintf fmt "<="

let pp_axiom fmt n pn (cmp,bound) =
  Format.fprintf fmt "@[axiom pr%i &m :@ %a %a@ %a.@]@ "
    n pp_prob pn pp_cmp cmp pp_bound bound 

let rec bound_indep ty = 
  match ty.ty_node with
  | BS lv -> Bbs lv
  | Bool  -> Bhalf
  | G _   -> Bf
  | Fq    -> Bf
  | Prod ts ->
    let rec aux ts = 
      match ts with
      | [] -> Bint 1
      | [t] -> bound_indep t
      | t::ts -> Bmul(bound_indep t, aux ts) in
    aux ts

let bound_rule rule gn ju subgoals = 
  match rule, subgoals with
  | Radmit, [] -> (gn,ju), (Eq,Bju(gn,ju))
  | Rconv, [_,b] -> (gn,ju), b
  | Rctxt_ev _, [_,b] -> (gn,ju), b
  | Rremove_ev _, [_,b] -> (gn,ju), b
  | Rmerge_ev _, [_,b] -> (gn,ju), b
  | Rrandom _, [_,b] -> (gn,ju), b
  | Rrnd_orcl _, [_,b] -> (gn,ju), b
  | Rexcept _,_ -> assert false 
  | Rexc_orcl _,_ -> assert false
  | Radd_test _,_ -> assert false
  | Rrw_orcl _,_ -> assert false
  | Rswap _, [_,b] -> (gn,ju), b
  | Rswap_orcl _, [_,b] -> (gn,ju), b
  | Rrnd_indep (_,i), [] -> 
    let ev = List.nth (destruct_Land ju.ju_ev) i in
    let bound = 
      (* TODO fixme sampling restriction *)
      if is_Eq ev then 
        let e,_ = destr_Eq ev in
        (Eq, bound_indep e.e_ty)
      else if is_Exists ev then assert false
      else assert false in
    (gn,ju), bound

  | Rassm_dec (_dir,_,_), [ju',(_, b)] -> 
    (gn,ju), (Le, Badd (Bsub (Bju(gn,ju), Bju ju'), b))
  | Rbad _,_ -> assert false
  | _,_ -> assert false

let pp_rule = function
  | Radmit -> "admit"
  | Rconv -> "conv"
  | Rctxt_ev _ -> "ctxt_ev"
  | Rremove_ev _ -> "remove_ev"
  | Rmerge_ev _ -> "merge_ev"
  | Rrandom _ -> "random"
  | Rrnd_orcl _ -> "rnd_orcl"
  | Rexcept _ -> "except"
  | Rexc_orcl _ -> "except_orcl"
  | Radd_test _ -> "add_test"
  | Rrw_orcl _ -> "rw_orcl"
  | Rswap _ -> "swap"
  | Rswap_orcl _ -> "swap_orcl"
  | Rrnd_indep _ -> "indep"
  | Rassm_dec _ ->  "assumption"
  | Rbad _ -> "bad"


let pp_rule fmt n gn ju rule subgoals = 
  let bound = bound_rule rule gn ju subgoals in
  pp_axiom fmt n (fst bound) (snd bound);
  Format.fprintf fmt "(* %s *)@ @ " (pp_rule rule);
  bound
    
let pp_proof fmt pft =
  let gc = ref 0 in
  let get_gc () = incr gc; !gc in

  let rec aux fmt pft = 
    let n = get_gc () in
    let gn = "G" ^ string_of_int n in
    let subgoals = List.map (aux fmt) pft.dr_subgoal in
    Format.fprintf fmt "%a@ " (pp_game gn) pft.dr_ju;
    pp_rule fmt n gn pft.dr_ju pft.dr_rule subgoals in
  
  ignore (aux fmt pft)
    
let pp_all fmt ts pft =
  Format.fprintf fmt "@[<v>";
  pp_lvars fmt ts.ts_lvars;
  pp_gvars fmt ts.ts_gvars;
  pp_bilinear fmt ts.ts_emdecls;
  pp_assumption fmt ts.ts_assms;
  let ginfo = game_info pft.dr_ju.ju_gdef in
  pp_adv_decl fmt ginfo;
  pp_proof fmt pft;

  Format.fprintf fmt "@]@."

let extract ts filename = 
  Extraction.extract ts filename

(*
  let ps = get_proof_state ts in
  let pft = get_proof ps in
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  pp_all fmt ts pft;
  close_out out
*)

  

  
    

