open Type
(* open Expr *)
(* open Game *)
open CoreRules
open TheoryState

module Ht = Hashtbl

let pp_lvar_mod fmt lv = 
  Format.fprintf fmt "BS_%s" (Lenvar.name lv)

let pp_lvar_ty fmt lv = 
  Format.fprintf fmt "%a.bitstring" pp_lvar_mod lv 

let pp_lvars fmt lvars = 
  if Ht.length lvars <> 0 then 
    let out _ lv = 
      Format.fprintf fmt "clone ABitstring as %a.@ " pp_lvar_mod lv
    in
    Format.fprintf fmt "(** { Bitstring declarations. } *)@ @ ";
    Format.fprintf fmt "require ABitstring.@ @ ";
    Ht.iter out lvars;
    Format.fprintf fmt "@ "

let pp_gvar_mod fmt gv = 
  Format.fprintf fmt "G%s" (Groupvar.name gv)

let pp_gvar_type fmt gv = 
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

let pp_bilinear _fmt _bvars = ()

let pp_proof _fmt _ps _pft = ()

let pp_all fmt ts pft =
  Format.fprintf fmt "@[<v>";
  pp_lvars fmt ts.ts_lvars;
  pp_gvars fmt ts.ts_gvars;
  pp_bilinear fmt ts.ts_emdecls;
  pp_proof fmt ts pft;
  Format.fprintf fmt "@]@."

let extract ts filename = 
  let pft = 
    match ts.ts_ps with
    | BeforeProof  (* FIXME: adapt after adding save and storing the proof tree in ClosedTheory *)
    | ClosedTheory -> tacerror "No derivation"
    | ActiveProof gs -> get_proof gs in
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  pp_all fmt ts pft;
  close_out out


  

  
    

