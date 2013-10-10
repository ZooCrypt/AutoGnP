open Type
open ExprSyntax
open Expr
open Game

module F = Format

let duni_Fq = (mk_Fq, [])
let duni_Bool = (mk_Bool, [])

let norm_exp e0 = 
  let go e =
    match e.e_node with
    | App (FOpp,_)
    | App (FInv,_)
    | App (FMinus,_)
    | App (FDiv,_)
    | Nary (FPlus,_)
    | Nary (FMult,_) -> Singular.norm e
    | _              -> e
  in e_map go e0

let mk_bb1 () =
  let c = (Vsym.mk "c" mk_Fq) in
  let d = (Vsym.mk "d" mk_Fq) in
  let e = (Vsym.mk "e" mk_Fq) in
  let h = (Vsym.mk "h" mk_Fq) in
  let b = (Vsym.mk "b" mk_Bool) in
  let i = (Vsym.mk "i" mk_Fq) in
  let r = (Vsym.mk "r" mk_Fq) in
  let i' = (Vsym.mk "i'" mk_Fq) in
  let b' = (Vsym.mk "b'" mk_Bool) in
  let m0 = (Vsym.mk "m0" mk_GT) in
  let m1 = (Vsym.mk "m1" mk_GT) in
  let mb = (Vsym.mk "m0" mk_GT) in

  let vc  = v c in
  let vd  = v d in
  let ve  = v e in
  let vh  = v h in
  let vb  = v b in
  let vi  = v i in
  let vr  = v r in
  let vi' = v i' in
  let vb' = v b' in
  let vm0 = v m0 in
  let vm1 = v m1 in
  let vmb = v mb in

  let o1 =
    (Osym.mk "kg" mk_Fq (mk_Prod [mk_G;mk_G]),
     [i],
     [ LGuard(mk_Not (mk_Eq vi vi'));
       LSamp(r,duni_Fq)
     ],
     tuple [ g ^: ((vc *: vd) +: (vr *: ((vd *: vi) +: vh)));
             g ^: vr]
     )
  in  
  [ GCall([i'],f0,[]);
    GSamp(c,duni_Fq);
    GSamp(d,duni_Fq);
    GSamp(e,duni_Fq);
    GSamp(h,duni_Fq);
    GSamp(b,duni_Bool);
    GCall([m0;m1],
           tuple [g ^: vc; g ^: vd; g ^: vh],[o1]);
    GLet([mb],ifte vb vm0 vm1);
    GCall( [b']
         , tuple
             [ vmb 
               &: ((em (g,g)) ^^: (vc *: vd *: ve));
              g ^: ve;
              g ^: (ve *: ((vd *: vi') +: vh))]
         , [o1]);

  ]

let main =
  let bb1 =
    catch_TypeError (fun () -> mk_bb1 ()) in
  F.printf "G1 =\n%a\n\n" pp_gdef bb1;
  let bb1' = map_gdef_exp norm_exp bb1 in
  F.printf "G2 =%a\n\n" pp_gdef bb1';

