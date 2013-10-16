open Expr
open Type
open ExprSyntax
open Game

let duni_Fq = (mk_Fq, [])
let duni_Bool = (mk_Bool, [])

let _ =
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
  let oname = Osym.mk "Gg" mk_Fq (mk_Prod [mk_G;mk_G]) in
  let aname1 = Asym.mk "A1" (mk_Prod []) mk_Fq in
  let aname2 = Asym.mk "A2" (mk_Prod [mk_G;mk_G;mk_G]) (mk_Prod [mk_GT;mk_GT]) in
  let aname3 = Asym.mk "A3" (mk_Prod [mk_GT; mk_G; mk_G]) mk_Bool in
  let o1 = 
    (oname,
     [i],
     [ LGuard (mk_Not (mk_Eq vi vi'));
       LSamp(r,(mk_Fq,[vi]))
     ],

      tuple [ g ^: ((vc *: vd) +: (vr *: ((vd *: vi) +: vh)));
             g ^: (vr /: (vi -: vi') /: (vr -: vi)) ]
      )
  in
  let g1 =
    [ GCall([i'],aname1,mk_Tuple [],[]);
      GSamp(c,duni_Fq);
      GSamp(d,duni_Fq);
      GSamp(e,duni_Fq);
      GSamp(h,duni_Fq);
      GSamp(b,duni_Bool);
      GCall([m0;m1],aname2,
             tuple [g ^: vc; g ^: vd; g ^: vh],[]);
      GLet(mb,ifte vb vm0 vm1);
      GCall( [b'], aname3
           , tuple
               [ vmb 
                 &: ((em (g,g)) ^^: (vc *: vd *: ve));
                 g ^: ve;
                 g ^: (ve *: ((vd *: vi') +: vh))]
           , [o1]);
    ]
  in
  let bb' = mk_Eq vb vb' in
  let ju =  mk_ju g1 bb' in
  Wf.wf_ju ju)