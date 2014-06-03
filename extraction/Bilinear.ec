require import PrimeField.
require CyclicGroup.

theory Bl.

clone import CyclicGroup.CG as G1.
clone import CyclicGroup.CG as G2.
clone import CyclicGroup.CG as GT.

op e : G1.group -> G2.group -> GT.group.

axiom e_g_g : e G1.g G2.g = GT.g.

axiom eND : e G1.g G2.g <> GT.g1.


axiom e_pow1 (g:G1.group) (x:t) f: e (g^x) f = (e g f)^x.
axiom e_pow2 (f:G2.group) x g: e g (f^x) = (e g f)^x.

lemma e_pow (g:G1.group) (f:G2.group) (x y:t) : e (g^x) (f^y) =  (e g f)^(x*y).
proof.
  by rewrite e_pow2 e_pow1 GT.pow_pow.
qed.

lemma e_mul1 x y g2: e x g2 * e y g2 = e (x*y) g2.
proof.
  by rewrite -(G1.gpow_log x) -(G1.gpow_log y) G1.mul_pow !e_pow1 GT.mul_pow.
qed.

lemma e_mul2 g1 x y: e g1 x * e g1 y = e g1 (x*y).
proof.
  by rewrite -(G2.gpow_log x) -(G2.gpow_log y) G2.mul_pow !e_pow2 GT.mul_pow.
qed.

lemma log_e (x:G1.group) (y:G2.group):
  log (e x y) = log x * log y.
proof.
  rewrite -{1}(G1.gpow_log x) -{1}(G2.gpow_log y) e_pow GT.log_pow F.mulA e_g_g GT.log_g;ringeq.
qed.

end Bl.
   
