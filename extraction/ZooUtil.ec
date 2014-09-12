require import Real.
require import Bool.

lemma le_abs_add1 : forall (x x0 : real), x <= `|x - x0| + x0
by [].

lemma le_abs_add2 : forall (x x0 : real), x0 <= `|x - x0| + x
by [].

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

instance bring with bool
  op rzero = false
  op rone  = true
  op add   = (^^)
  op mul   = (/\)

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrK     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof mulrK     by smt.

require import Real.

lemma neqeqf_rw (a b:'a) : (a <> b) = false <=> a = b by smt.
lemma eqeqt_rw (a b:'a) : (a = b) = true <=> a = b by smt.

hint rewrite Ring.rw_algebra : neqeqf_rw eqeqt_rw.

(*
require import Real.

lemma toto1 (x y z: real) : y + x^2 = y => (x*(x + y) - y)*z = z*x*y - y*z.
intros H.
ringeq H.
qed.

lemma foo1 (x y : real) : ((x + 0%r = y) /\ (x = y)) = (x = y).
algebra.
qed.

lemma toto (b:bool) : ((true ^^ b) /\ b) = false.
algebra.
qed.

lemma foo (x y:real):
  ((x + 0%r = y) /\ (x = y) /\ (x = x)) = (x = y).
algebra.
qed.
*)