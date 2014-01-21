require import Real.
require import ZooUtil.
(** { Bitstring declarations. } *)

require AWord.

clone import AWord as BS_k.

(** { Group declarations. } *)

require import PrimeField.
import F.
require CyclicGroup.

clone import CyclicGroup.CG as G.

(** { operators declarations. } *)

op H : G.group -> BS_k.word.

(** { Assumptions. } *)

module type Adv_ddh = {
  proc main (gx:G.group, gy:G.group, gxy:G.group) : bool
}.

module G_ddh1(A:Adv_ddh) = {
  proc main() : bool = {
    var _res: bool;
    var gx: G.group;
    var gy: G.group;
    var gxy: G.group;
    var y: F.t;
    var x: F.t;
    x = $FDistr.dt;
    y = $FDistr.dt;
    gx = G.g ^ x;
    gy = G.g ^ y;
    gxy = G.g ^ (x * y);
    _res = A.main((gx, gy, gxy));
    return _res;
  }
}.

module G_ddh2(A:Adv_ddh) = {
  proc main() : bool = {
    var _res: bool;
    var gx: G.group;
    var gy: G.group;
    var gxy: G.group;
    var z: F.t;
    var y: F.t;
    var x: F.t;
    x = $FDistr.dt;
    y = $FDistr.dt;
    z = $FDistr.dt;
    gx = G.g ^ x;
    gy = G.g ^ y;
    gxy = G.g ^ z;
    _res = A.main((gx, gy, gxy));
    return _res;
  }
}.

module type Adv_es = {
  proc main (h:BS_k.word) : bool
}.

module G_es1(A:Adv_es) = {
  proc main() : bool = {
    var _res: bool;
    var h: BS_k.word;
    var x: F.t;
    x = $FDistr.dt;
    h = H (G.g ^ x);
    _res = A.main((h));
    return _res;
  }
}.

module G_es2(A:Adv_es) = {
  proc main() : bool = {
    var _res: bool;
    var h: BS_k.word;
    h = $BS_k.Dword.dword;
    _res = A.main((h));
    return _res;
  }
}.

module type Orcl = {
  
}.

module type Adv (O:Orcl) = {
   proc aA2 (_ : (G.group * BS_k.word)) : bool {}
   proc aA1 (_ : G.group) : (BS_k.word * BS_k.word) {}
}.

module M(A:Adv) = {
  var c: (G.group * BS_k.word)
  var pk: G.group
  var he, mb, m0, m1: BS_k.word
  var b', b: bool
  var y, sk: F.t
  
  module O = {
    
  }
  
  module A = A(O)
  
  proc main() : unit = {
    sk = $FDistr.dt;
    pk = G.g ^ sk;
    (m0, m1) = A.aA1(pk);
    b = ${0,1};
    mb = b ? m0 : m1;
    y = $FDistr.dt;
    he = H (pk ^ y);
    c = (G.g ^ y, mb ^ he);
    b' = A.aA2(c);
    
  }
}.

module Fadv_es(A:Adv) = {
  var h, m0, m1: BS_k.word
  var b', b: bool
  var y, sk: F.t
  
  module O = {
    
  }
  
  module A = A(O)
  
  proc main(_h: BS_k.word) : bool = {
    var _res: bool;
    h = _h;
    sk = $FDistr.dt;
    y = $FDistr.dt;
    (m0, m1) = A.aA1(G.g ^ sk);
    b = ${0,1};
    b' = A.aA2((G.g ^ y, (b ? m0 : m1) ^ h));
    _res = b = b';
    return _res;
  }
}.

module Fadv_ddh(A:Adv) = {
  var gsky, gy, gsk: G.group
  var m0, m1: BS_k.word
  var b', b: bool
  
  module O = {
    
  }
  
  module A = A(O)
  
  proc main(_gx: G.group, _gy: G.group, _gxy: G.group) : bool = {
    var _res: bool;
    gsk = _gx;
    gy = _gy;
    gsky = _gxy;
    (m0, m1) = A.aA1(gsk);
    b = ${0,1};
    b' = A.aA2((gy, (b ? m0 : m1) ^ H gsky));
    _res = b = b';
    return _res;
  }
}.

section.

  declare module A : Adv {M, Fadv_es, Fadv_ddh}.
  
  local module M0(A:Adv) = {
    var h, m0, m1: BS_k.word
    var b', b: bool
    var y, sk: F.t
    
    module O = {
      
    }
    
    module A = A(O)
    
    proc main() : unit = {
      sk = $FDistr.dt;
      y = $FDistr.dt;
      (m0, m1) = A.aA1(G.g ^ sk);
      h = $BS_k.Dword.dword;
      b' = A.aA2((G.g ^ y, h));
      b = ${0,1};
      
    }
  }.
  
  local lemma Lem:
    forall &m, Pr[M0(A).main() @ &m: M0.b = M0.b'] <= 1%r / 2%r.
  proof.
    intros &m; byphoare (_ : true ==> M0.b = M0.b') => //.
    proc; rnd ((=) M0.b'); conseq (_ : _ ==> true); last by [].
    simplify; intros &m1;progress.
    apply Real.eq_le;apply Bool.Dbool.mu_x_def.
  qed.
  
  local module M1(A:Adv) = {
    var z1, h, m0, m1: BS_k.word
    var b', b: bool
    var y, sk: F.t
    
    module O = {
      
    }
    
    module A = A(O)
    
    proc main() : unit = {
      sk = $FDistr.dt;
      y = $FDistr.dt;
      (m0, m1) = A.aA1(G.g ^ sk);
      b = ${0,1};
      h = $BS_k.Dword.dword;
      z1 = (b ? m0 : m1) ^ h;
      b' = A.aA2((G.g ^ y, (b ? m0 : m1) ^ z1));
      
    }
  }.
  
  local lemma Lem0:
    forall &m,
      Pr[M1(A).main() @ &m: M1.b = M1.b'] =
      Pr[M0(A).main() @ &m: M0.b = M0.b'].
  proof.
    intros &m;byequiv (_: ={glob A} ==> (M1.b{1} = M1.b'{1}) =
                                        (M0.b{2} = M0.b'{2}));
      [ proc | by [] | by intros &m1 &m2 ->].
    swap{2} 6 -2.
    (* conv *)admit.
  qed.
  
  local lemma Lem1:
    forall &m, Pr[M1(A).main() @ &m: M1.b = M1.b'] <= 1%r / 2%r.
  proof.
    intros &m; rewrite {1}(Lem0 &m);apply (Lem &m).
  qed.
  
  local module M2(A:Adv) = {
    var h, m0, m1: BS_k.word
    var b', b: bool
    var y, sk: F.t
    
    module O = {
      
    }
    
    module A = A(O)
    
    proc main() : unit = {
      sk = $FDistr.dt;
      y = $FDistr.dt;
      (m0, m1) = A.aA1(G.g ^ sk);
      b = ${0,1};
      h = $BS_k.Dword.dword;
      b' = A.aA2((G.g ^ y, (b ? m0 : m1) ^ h));
      
    }
  }.
  
  local lemma Lem2:
    forall &m,
      Pr[M2(A).main() @ &m: M2.b = M2.b'] =
      Pr[M1(A).main() @ &m: M1.b = M1.b'].
  proof.
    intros &m;byequiv (_: ={glob A} ==> (M2.b{1} = M2.b'{1}) =
                                        (M1.b{2} = M1.b'{2}));
      [ proc | by [] | by intros &m1 &m2 ->].
    sim.
    wp 5 5.
    rnd (fun v, (M1.b{2} ? M1.m0{2} : M1.m1{2}) ^ v)
      (fun v, (M1.b{2} ? M1.m0{2} : M1.m1{2}) ^ v).
    conseq (_: _ ==>
      (M2.y{1} = M1.y{2}) /\
      ((M2.b{1} = M1.b{2}) /\
       ((M2.m0{1} = M1.m0{2}) /\
        ((M2.m1{1} = M1.m1{2}) /\ (M2.sk{1} = M1.sk{2})))) /\ ={glob A}).
      progress.
        by smt. (* improve *)
        by smt. (* improve *)
        by admit. (*ringeq. FIXME *)
        by admit. (*ringeq. FIXME *)
      by apply eq_sym.
    sim.
  qed.
  
  local lemma Lem3:
    forall &m, Pr[M2(A).main() @ &m: M2.b = M2.b'] <= 1%r / 2%r.
  proof.
    intros &m; rewrite {1}(Lem2 &m);apply (Lem1 &m).
  qed.
  
  local module M3(A:Adv) = {
    var h, m0, m1: BS_k.word
    var b', b: bool
    var y, sk: F.t
    
    module O = {
      
    }
    
    module A = A(O)
    
    proc main() : unit = {
      h = $BS_k.Dword.dword;
      sk = $FDistr.dt;
      y = $FDistr.dt;
      (m0, m1) = A.aA1(G.g ^ sk);
      b = ${0,1};
      b' = A.aA2((G.g ^ y, (b ? m0 : m1) ^ h));
      
    }
  }.
  
  local lemma Lem4:
    forall &m,
      Pr[M3(A).main() @ &m: M3.b = M3.b'] =
      Pr[M2(A).main() @ &m: M2.b = M2.b'].
  proof.
    intros &m;byequiv (_: ={glob A} ==> (M3.b{1} = M3.b'{1}) =
                                        (M2.b{2} = M2.b'{2}));
      [ proc | by [] | by intros &m1 &m2 ->].
    swap{1} 1 4.
    sim.
  qed.
  
  local lemma Lem5:
    forall &m, Pr[M3(A).main() @ &m: M3.b = M3.b'] <= 1%r / 2%r.
  proof.
    intros &m; rewrite {1}(Lem4 &m);apply (Lem3 &m).
  qed.
  
  local module M4(A:Adv) = {
    var h, m0, m1: BS_k.word
    var b', b: bool
    var u, y, sk: F.t
    
    module O = {
      
    }
    
    module A = A(O)
    
    proc main() : unit = {
      u = $FDistr.dt;
      h = H (G.g ^ u);
      sk = $FDistr.dt;
      y = $FDistr.dt;
      (m0, m1) = A.aA1(G.g ^ sk);
      b = ${0,1};
      b' = A.aA2((G.g ^ y, (b ? m0 : m1) ^ h));
      
    }
  }.
  
  local lemma Lem6:
    forall &m,
      Pr[M4(A).main() @ &m: M4.b = M4.b'] =
      Pr[G_es1(Fadv_es(A)).main() @ &m: res].
  proof.
     intros &m; byequiv (_: ={glob A} ==> (M4.b{1} = M4.b'{1}) = res{2}) => //.
    by proc; inline{2} Fadv_es(A).main; wp; sim.
  qed.
  
  local lemma Lem7:
    forall &m,
      Pr[M3(A).main() @ &m: M3.b = M3.b'] =
      Pr[G_es2(Fadv_es(A)).main() @ &m: res].
  proof.
     intros &m; byequiv (_: ={glob A} ==> (M3.b{1} = M3.b'{1}) = res{2}) => //.
    by proc; inline{2} Fadv_es(A).main; wp; sim.
  qed.
  
  local lemma Lem8:
    forall &m,
      Pr[M4(A).main() @ &m: M4.b = M4.b'] <=
      `|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
        Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
      Pr[M3(A).main() @ &m: M3.b = M3.b'].
  proof.
    intros &m;rewrite (Lem6 &m) (Lem7 &m);apply ZooUtil.le_abs_add1.
  qed.
  
  local lemma Lem9:
    forall &m,
      Pr[M4(A).main() @ &m: M4.b = M4.b'] <=
      `|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
        Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
      1%r / 2%r.
  proof.
    intros &m.
    apply (real_le_trans Pr[M4(A).main() @ &m: M4.b = M4.b']
    (`|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
       Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
     Pr[M3(A).main() @ &m: M3.b = M3.b'])
    (`|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
       Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
     1%r / 2%r)).
    apply (Lem8 &m).
    apply Real.addleM; first by [].
    by apply (Lem5 &m).
  qed.
  
  local module M5(A:Adv) = {
    var m0, m1: BS_k.word
    var b', b: bool
    var u, y, sk: F.t
    
    module O = {
      
    }
    
    module A = A(O)
    
    proc main() : unit = {
      u = $FDistr.dt;
      sk = $FDistr.dt;
      y = $FDistr.dt;
      (m0, m1) = A.aA1(G.g ^ sk);
      b = ${0,1};
      b' = A.aA2((G.g ^ y, (b ? m0 : m1) ^ H (G.g ^ u)));
      
    }
  }.
  
  local lemma Lem10:
    forall &m,
      Pr[M5(A).main() @ &m: M5.b = M5.b'] =
      Pr[M4(A).main() @ &m: M4.b = M4.b'].
  proof.
    intros &m;byequiv (_: ={glob A} ==> (M5.b{1} = M5.b'{1}) =
                                        (M4.b{2} = M4.b'{2}));
      [ proc | by [] | by intros &m1 &m2 ->].
    (* conv *)admit.
  qed.
  
  local lemma Lem11:
    forall &m,
      Pr[M5(A).main() @ &m: M5.b = M5.b'] <=
      `|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
        Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
      1%r / 2%r.
  proof.
    intros &m; rewrite {1}(Lem10 &m);apply (Lem9 &m).
  qed.
  
  local module M6(A:Adv) = {
    var gsky, gy, gsk: G.group
    var m0, m1: BS_k.word
    var b', b: bool
    var u, y, sk: F.t
    
    module O = {
      
    }
    
    module A = A(O)
    
    proc main() : unit = {
      sk = $FDistr.dt;
      y = $FDistr.dt;
      u = $FDistr.dt;
      gsk = G.g ^ sk;
      gy = G.g ^ y;
      gsky = G.g ^ u;
      (m0, m1) = A.aA1(gsk);
      b = ${0,1};
      b' = A.aA2((gy, (b ? m0 : m1) ^ H gsky));
      
    }
  }.
  
  local lemma Lem12:
    forall &m,
      Pr[M6(A).main() @ &m: M6.b = M6.b'] =
      Pr[M5(A).main() @ &m: M5.b = M5.b'].
  proof.
    intros &m;byequiv (_: ={glob A} ==> (M6.b{1} = M6.b'{1}) =
                                        (M5.b{2} = M5.b'{2}));
      [ proc | by [] | by intros &m1 &m2 ->].
    swap{2} 1 2.
    (* conv *)admit.
  qed.
  
  local lemma Lem13:
    forall &m,
      Pr[M6(A).main() @ &m: M6.b = M6.b'] <=
      `|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
        Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
      1%r / 2%r.
  proof.
    intros &m; rewrite {1}(Lem12 &m);apply (Lem11 &m).
  qed.
  
  local module M7(A:Adv) = {
    var gsky, gy, gsk: G.group
    var m0, m1: BS_k.word
    var b', b: bool
    var y, sk: F.t
    
    module O = {
      
    }
    
    module A = A(O)
    
    proc main() : unit = {
      sk = $FDistr.dt;
      y = $FDistr.dt;
      gsk = G.g ^ sk;
      gy = G.g ^ y;
      gsky = G.g ^ (sk * y);
      (m0, m1) = A.aA1(gsk);
      b = ${0,1};
      b' = A.aA2((gy, (b ? m0 : m1) ^ H gsky));
      
    }
  }.
  
  local lemma Lem14:
    forall &m,
      Pr[M7(A).main() @ &m: M7.b = M7.b'] =
      Pr[G_ddh1(Fadv_ddh(A)).main() @ &m: res].
  proof.
     intros &m; byequiv (_: ={glob A} ==> (M7.b{1} = M7.b'{1}) = res{2}) => //.
    by proc; inline{2} Fadv_ddh(A).main; wp; sim.
  qed.
  
  local lemma Lem15:
    forall &m,
      Pr[M6(A).main() @ &m: M6.b = M6.b'] =
      Pr[G_ddh2(Fadv_ddh(A)).main() @ &m: res].
  proof.
     intros &m; byequiv (_: ={glob A} ==> (M6.b{1} = M6.b'{1}) = res{2}) => //.
    by proc; inline{2} Fadv_ddh(A).main; wp; sim.
  qed.
  
  local lemma Lem16:
    forall &m,
      Pr[M7(A).main() @ &m: M7.b = M7.b'] <=
      `|Pr[G_ddh1(Fadv_ddh(A)).main() @ &m: res] -
        Pr[G_ddh2(Fadv_ddh(A)).main() @ &m: res]| +
      Pr[M6(A).main() @ &m: M6.b = M6.b'].
  proof.
    intros &m;rewrite (Lem14 &m) (Lem15 &m);apply ZooUtil.le_abs_add1.
  qed.
  
  local lemma Lem17:
    forall &m,
      Pr[M7(A).main() @ &m: M7.b = M7.b'] <=
      `|Pr[G_ddh1(Fadv_ddh(A)).main() @ &m: res] -
        Pr[G_ddh2(Fadv_ddh(A)).main() @ &m: res]| +
      (`|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
         Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
       1%r / 2%r).
  proof.
    intros &m.
    apply (real_le_trans Pr[M7(A).main() @ &m: M7.b = M7.b']
    (`|Pr[G_ddh1(Fadv_ddh(A)).main() @ &m: res] -
       Pr[G_ddh2(Fadv_ddh(A)).main() @ &m: res]| +
     Pr[M6(A).main() @ &m: M6.b = M6.b'])
    (`|Pr[G_ddh1(Fadv_ddh(A)).main() @ &m: res] -
       Pr[G_ddh2(Fadv_ddh(A)).main() @ &m: res]| +
     (`|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
        Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
      1%r / 2%r))).
    apply (Lem16 &m).
    apply Real.addleM; first by [].
    by apply (Lem13 &m).
  qed.
  
  local module M8(A:Adv) = {
    var m0, m1: BS_k.word
    var b', b: bool
    var y, sk: F.t
    
    module O = {
      
    }
    
    module A = A(O)
    
    proc main() : unit = {
      sk = $FDistr.dt;
      y = $FDistr.dt;
      (m0, m1) = A.aA1(G.g ^ sk);
      b = ${0,1};
      b' = A.aA2((G.g ^ y, (b ? m0 : m1) ^ H (G.g ^ (sk * y))));
      
    }
  }.
  
  local lemma Lem18:
    forall &m,
      Pr[M8(A).main() @ &m: M8.b = M8.b'] =
      Pr[M7(A).main() @ &m: M7.b = M7.b'].
  proof.
    intros &m;byequiv (_: ={glob A} ==> (M8.b{1} = M8.b'{1}) =
                                        (M7.b{2} = M7.b'{2}));
      [ proc | by [] | by intros &m1 &m2 ->].
    (* conv *)admit.
  qed.
  
  local lemma Lem19:
    forall &m,
      Pr[M8(A).main() @ &m: M8.b = M8.b'] <=
      `|Pr[G_ddh1(Fadv_ddh(A)).main() @ &m: res] -
        Pr[G_ddh2(Fadv_ddh(A)).main() @ &m: res]| +
      (`|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
         Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
       1%r / 2%r).
  proof.
    intros &m; rewrite {1}(Lem18 &m);apply (Lem17 &m).
  qed.
  
  local lemma Lem20:
    forall &m,
      Pr[M(A).main() @ &m: M.b = M.b'] = Pr[M8(A).main() @ &m: M8.b = M8.b'].
  proof.
    intros &m;byequiv (_: ={glob A} ==> (M.b{1} = M.b'{1}) =
                                        (M8.b{2} = M8.b'{2}));
      [ proc | by [] | by intros &m1 &m2 ->].
    swap{2} 2 2.
    (* conv *)admit.
  qed.
  
  local lemma Lem21:
    forall &m,
      Pr[M(A).main() @ &m: M.b = M.b'] <=
      `|Pr[G_ddh1(Fadv_ddh(A)).main() @ &m: res] -
        Pr[G_ddh2(Fadv_ddh(A)).main() @ &m: res]| +
      (`|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
         Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
       1%r / 2%r).
  proof.
    intros &m; rewrite {1}(Lem20 &m);apply (Lem19 &m).
  qed.
  
  lemma conclusion:
    forall &m,
      Pr[M(A).main() @ &m: M.b = M.b'] <=
      `|Pr[G_ddh1(Fadv_ddh(A)).main() @ &m: res] -
        Pr[G_ddh2(Fadv_ddh(A)).main() @ &m: res]| +
      (`|Pr[G_es1(Fadv_es(A)).main() @ &m: res] -
         Pr[G_es2(Fadv_es(A)).main() @ &m: res]| +
       1%r / 2%r).
  proof.
    apply Lem21.
  qed.

end section.
