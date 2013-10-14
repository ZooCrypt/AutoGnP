open Type
open ExprSyntax
open Expr
open Game
open CoreRule
open Rules

module F = Format

let duni_Fq = (mk_Fq, [])
let duni_Bool = (mk_Bool, [])

let main =
  catch_TypeError (fun () ->
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
  let mb = (Vsym.mk "mb" mk_GT) in

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
  let oname = Osym.mk "kg" mk_Fq (mk_Prod [mk_G;mk_G]) in
  let o1 = 
    (oname,
     [i],
     [ LGuard(mk_Not (mk_Eq vi vi'));
       LSamp(r,duni_Fq)
     ],
     tuple [ g ^: ((vc *: vd) +: (vr *: ((vd *: vi) +: vh)));
             g ^: vr]
     )
  in
  let g1 =
    [ GCall([i'],mk_Tuple [],[]);
      GSamp(c,duni_Fq);
      GSamp(d,duni_Fq);
      GSamp(e,duni_Fq);
      GSamp(h,duni_Fq);
      GSamp(b,duni_Bool);
      GCall([m0;m1],
             tuple [g ^: vc; g ^: vd; g ^: vh],[]);
      GLet(mb,ifte vb vm0 vm1);
      GCall( [b']
           , tuple
               [ vmb 
                 &: ((em (g,g)) ^^: (vc *: vd *: ve));
                 g ^: ve;
                 g ^: (ve *: ((vd *: vi') +: vh))]
           , [o1]);
    ]
  in
 
  let bb' = mk_Eq vb vb' in
  let ps =  [mk_ju g1 bb'] in
  let vstar = Vsym.mk "*" mk_Fq in
  let star = mk_V vstar in
  F.printf "%a" pp_ps ps;
  let ps = apply rnorm ps in
  F.printf "%a" pp_ps ps;
  let ps = apply (rrandom 4 (vstar, star -: (vd *: vi'))
                            (vstar, star +: (vd *: vi'))) ps in
  F.printf "%a" pp_ps ps;
  let ps = apply rnorm ps in
  F.printf "%a" pp_ps ps;
  let ps = apply (rrandom_oracle (7,0,1)
                    (vstar, (star -: vc) /: (vi -: vi')) (vstar, star *: (vi -: vi') +: vc)) ps in
  F.printf "%a" pp_ps ps;
  let ps = apply rnorm ps in
  F.printf "%a" pp_ps ps;
  let ps = apply (rswap 0 3) ps in
  F.printf "%a" pp_ps ps;
  let gc = (Vsym.mk "gc" mk_G) in
  let vgc = mk_V gc in
  let gd = (Vsym.mk "gd" mk_G) in
  let vgd = mk_V gd in
  let ge = (Vsym.mk "ge" mk_G) in
  let vge = mk_V ge in
  let gu = (Vsym.mk "gu" mk_GT) in
  let vgu = mk_V gu in
  let ii' = vi -: vi' in
  let ju = List.hd ps in
  let h = match get_ju_gcmd ju 4 with GSamp(x,_) -> x | _ -> assert false in
  let vh = mk_V h in
  let r = match get_ju_lcmd ju (7, 0, 1)  with
    | _,_,(_,LSamp(r, _),_), _ -> r  | _ -> assert false in
  let vr = mk_V r in
  let o2 = 
    (oname,
     [i],
     [ LGuard(mk_Not (mk_Eq vi vi'));
       LSamp(r,duni_Fq)
     ],
     tuple [ (vgc ^: ((f0 -: vh)/:ii')) **: 
               (vgd ^: vr) **: 
               (g ^: ((vh *: vr)/:ii'));
             (vgc ^: ((f0 -: f1)/:ii')) **: (g ^: (vr/:ii'))]
    ) in
  let g2 =
    [ GSamp(c,duni_Fq);
      GSamp(d,duni_Fq);
      GSamp(e,duni_Fq);
      GLet (gc, g ^: vc);
      GLet (gd, g ^: vd);
      GLet (ge, g ^: ve);
      GLet (gu, em(g,g) ^^: (mk_FMult [vc;vd;ve]));
      GCall([i'],mk_Tuple [],[]);
      GSamp(h,duni_Fq);
      GSamp(b,duni_Bool);
      GCall([m0;m1],
             tuple [vgc; vgd;  (vgd ^: (f0 -:vi')) **: (g ^: vh)],[]);
      GLet(mb,ifte vb vm0 vm1);
      GCall( [b']
           , tuple
               [ vmb &: vgu;
                 vge;
                 vge ^: vh]
           , [o2]);
    ] in
  let ju2 = {ju_gdef = g2; ju_ev = bb'} in 
  let ps = apply (rconv ju2) ps in
  F.printf "%a" pp_ps ps;
  let ps = apply (rbddh "u") ps in
  F.printf "%a" pp_ps ps;
  )


