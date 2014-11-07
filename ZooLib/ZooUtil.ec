require import Real.
require import Bool.
require import Distr.
require import FSet.

lemma le_abs_add1 : forall (x x0 : real), x <= `|x - x0| + x0
by [].

lemma le_abs_add2 : forall (x x0 : real), x0 <= `|x - x0| + x
by [].

lemma mulleM (x y z1 z2 : real): 0%r <= z1 <= z2 => 0%r <= x <= y => x * z1 <= y * z2.    
proof. 
  move=> H1 H2.
  apply (real_le_trans _ (x * z2)).
  rewrite !(Real.Comm.Comm x);apply mulrMle;smt.
  apply mulrMle;smt.
qed.

lemma iff_and (x1 x2 x1' x2' : bool) : 
  (x1 <=> x1') => (x2 <=> x2') =>
  (x1 /\ x2) <=> (x1' /\ x2').
proof. trivial. qed.
  
lemma iff_eq (x1 x2 x1' x2' : 'a) : 
  (x1 = x1') => (x2 = x2') =>
  ((x1 = x2) <=> (x1' = x2')).
proof. trivial. qed.

lemma iff_neq (x1 x2 x1' x2' : 'a) : 
  (x1 = x1') => (x2 = x2') =>
  ((x1 <> x2) <=> (x1' <> x2')).
proof. trivial. qed. 

op oif b (x1 x2:'a) = if b then x1 else x2.

lemma if_oif b (x1 x2:'a) : (if b then x1 else x2) = oif b x1 x2 by trivial.
hint rewrite Ring.rw_algebra : if_oif.

import FSet.Dexcepted.

lemma in_excepted_diff (d:'a distr) a1 a2:
   in_supp a1 (d \ single a2) => a1 <> a2 by [].
