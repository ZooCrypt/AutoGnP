require import Real.
require import Bool.
require import Distr.
require import FSet.

lemma real_mulleMl (x y z:real) : 0%r < x => y <= z => x * y <= x * z
by [].

lemma abs_add_minus x y y' z : 0%r <= x => y = y' => x <= z => `|((x + y) - y')| <= z
by [].
  
lemma abs_minus_xx (x:real): `|x - x| = 0%r
by [].

lemma abs_minusC (x y:real): `|x - y| = `|y - x|
by [].

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

(*op oif b (x1 x2:'a) = if b then x1 else x2.

lemma if_oif b (x1 x2:'a) : (if b then x1 else x2) = oif b x1 x2 by trivial.
hint rewrite Ring.rw_algebra : if_oif. *)

import FSet.Dexcepted.

lemma in_excepted_diff (d:'a distr) a1 a2:
   in_supp a1 (d \ single a2) => a1 <> a2 by [].

lemma nosmt dist_le_trans r1 r2 r3 p1 p2 : 
   `|r1 - r2| <= p1 => 
   `|r2 - r3| <= p2 => 
   `|r1 - r3| <= p1 + p2
by [].

lemma nosmt dist_eq_trans r1 r2 r3 p2 : 
   `|r1 - r2| = 0%r => 
   `|r2 - r3| = p2 => 
   `|r1 - r3| = p2
by [].

lemma nosmt bound_le_trans r1 r2 p1 p2 : 
   `|r1 - r2| <= p1 => r2 <= p2 => 
   r1 <= p1 + p2
by [].

lemma nosmt bound_eq_trans r1 r2 p2 : 
   `|r1 - r2| <= 0%r => r2 = p2 => 
   r1 = p2
by [].

lemma nosmt real_lt_le (r1 r2:real): r1 < r2 => r1 <= r2
by [].

lemma nosmt real_eq_le (r1 r2:real): r1 = r2 => r1 <= r2
by [].

lemma nosmt bound_eq_eq_trans (r1 r2 p2:real): 
   r1 = r2 => r2 = p2 => r1 = p2
by [].

lemma nosmt bound_eq_le_trans (r1 r2 p2:real): 
   r1 = r2 => r2 <= p2 => r1 <= p2
by [].

lemma nosmt dist_eq_eq_trans (r1 r2 r3 p2:real): 
   r1 = r2 => `|r2 - r3| = p2 => `|r1 - r3| = p2
by [].

lemma nosmt dist_eq_le_trans (r1 r2 r3 p2:real): 
   r1 = r2 => `|r2 - r3| <= p2 => `|r1 - r3| <= p2
by [].

lemma nosmt bound_split_eq (r1 r2 r3 p2 p3:real): 
  r1 = r2 + r3 => r2 = p2 => r3 = p3 => r1 = p2 + p3
by [].


hint rewrite Ring.rw_algebra : Logic.eqT Logic.neqF.

(* List *)
require import List.

lemma nosmt any_congr (f1 f2:'a -> bool) (l:'a list): 
   (forall a, f1 a <=> f2 a) => any f1 l <=> any f2 l.
proof.
  move=> H;rewrite -eq_iff;congr;apply fun_ext=> x;rewrite eq_iff;apply H.
qed.

lemma nosmt all_congr (f1 f2:'a -> bool) (l:'a list): 
    (forall a, f1 a <=> f2 a) => all f1 l <=> all f2 l.
proof.
  move=> H;rewrite -eq_iff;congr;apply fun_ext=> x;rewrite eq_iff;apply H.
qed.

lemma nosmt any_impl (f1 f2:'a -> bool) (l:'a list): 
   (forall a, f1 a => f2 a) => any f1 l => any f2 l.
proof.
  move=> H;rewrite /List.any;progress. by exists x;progress;apply H.
qed.

lemma nosmt all_impl (f1 f2:'a -> bool) (l:'a list): 
    (forall a, f1 a => f2 a) => all f1 l => all f2 l.
proof.
  by move=> H;rewrite /List.all;progress;apply H;apply H0.
qed.

lemma nosmt le_trans_sub (x y z w:real): 0%r <= z <= 1%r => x + y <= w => x + y - z <= w
by [].






