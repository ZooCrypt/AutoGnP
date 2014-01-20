require import PrimeField.

theory CG.
type group.

op g:group. (* the generator *)
op ( * ): group -> group -> group.   (* multiplication of group elements *)
op [-]  : group -> group.            (* inverse of the multiplication *) (* Why [/] do not work? *)
op ( / ): group -> group -> group.   (* division *)
op ( ^ ): group -> t -> group.       (* exponentiation *)
op log  : group -> t.                (* discrete logarithm *)

axiom inv_def (a:group): - a = g ^ (-log a).
axiom div_def (a b:group): g^(log a - log b) = a / b.

axiom mul_pow g (x y:t): g ^ x * g ^ y = g ^ (x + y).

axiom pow_pow g (x y:t): (g ^ x) ^ y = g ^ (x * y).

axiom pow_log (a:group): g ^ (log a) = a.

axiom log_pow (x:t): log (g ^ x) = x.

lemma pow_mul (g1 g2:group) x: g1^x * g2^x = (g1*g2)^x.
proof.
  rewrite -{1}(pow_log g1) -{1}(pow_log g2) !pow_pow mul_pow.
  by rewrite !(F.mulC _ x) mulfDl F.mulC -pow_pow -mul_pow !pow_log.
qed.

lemma pow_opp (x:group) (p:F.t): x^(-p) = -(x^p).
proof.
  rewrite inv_def. 
  cut -> : -p = (-F.one) * p by ringeq.
  cut -> : -log (x ^ p) = (-F.one) * log(x^p) by ringeq.
  by rewrite !(F.mulC (-F.one)) -!pow_pow pow_log.
qed.

op g1 = g ^ F.zero.
op ( ** ) (g1 g2:group) = g ^ (log g1 * log g2).
op ( ^^ ) (g1:group) (i:int) = g ^ ((log g1)^i). 
op ofint (i:int) = g ^ (F.ofint i). 

lemma mulC (x y: group): x * y = y * x.
proof. 
  by rewrite -(pow_log x) -(pow_log y) mul_pow;smt. 
qed.

lemma mulA (x y z: group): x * (y * z) = x * y * z.
proof. 
  by rewrite -(pow_log x) -(pow_log y) -(pow_log z) !mul_pow;smt. 
qed.

lemma mul1 x: g1 * x = x.
proof.
  by rewrite /g1 -(pow_log x) mul_pow;smt.
qed.

lemma divK (a:group): a / a = g1.
proof strict.
  by rewrite -div_def sub_def addfN.
qed.

lemma nosmt log_bij x y: x = y <=> log x = log y. 
proof. smt. qed.

lemma nosmt pow_bij (x y:F.t): x = y <=> g^x =g^y.
proof strict. smt. qed.

lemma log_g : log g = F.one.
proof strict.
 cut H: log g - log g = F.one + -log g by smt.
 cut H1: log g = log g + F.one + -log g; smt.
qed.

lemma g_neq0 : g1 <> g.
proof.
  rewrite /g1 -{2}(pow_log g) log_g -pow_bij;smt.
qed.

lemma mulN (x:group): x * -x = g1.
proof.
  rewrite inv_def -{1}(pow_log x) mul_pow;smt. 
qed.

lemma mulmulC (x y:group): x ** y = y ** x.
proof.
 rewrite /( ** );smt.
qed.

lemma add_log (x y:group): log x + log y = log (x * y)
by smt.

lemma mulmulrDl (x y z:group): x ** (y * z) = (x ** y) * (x ** z).
proof.
 rewrite /( ** ) -add_log mul_pow -pow_bij;ringeq.
qed.

instance ring with group
  op rzero = g1
  op rone  = g
  op add   = CG.( * )
  op opp   = CG.([-])
  op mul   = ( ** )
  op expr  = ( ^^ ) 
  op sub   = CG.(/)
  op ofint = CG.ofint
  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof expr0     by smt
  proof exprS     by smt
  proof subrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.

(* TODO rename *)

lemma cross_iff : forall (a b c d:group), (a * c) = (b * d) => (a = b <=> c = d). 
proof.
 intros a b c d Heq;split;intros Heq';subst. 
 cut -> : d = b * c * [-] b;[rewrite Heq | ];ringeq.
 cut -> : b = a * d * [-]d;[rewrite Heq | ];ringeq.
qed.

lemma cross_iffS : forall (a b c d:group), (b * c) = (a * d) => (a = b <=> c = d). 
proof.
  by intros a b c d Heq;rewrite eq_sym;apply cross_iff. 
qed.

lemma sum_opp_iff : forall (a b c d:group), (a * [-]b) = (c * [-]d) => (a = b <=> c = d). 
proof.
 intros a b c d Heq;split;intros Heq';subst.
 cut -> : c = b * [-] b * d;[rewrite Heq | ];ringeq.
 cut -> : a = d * [-]d * b;[rewrite -Heq | ];ringeq.
qed.

lemma eq_mul_div (x1 x2 y1 y2:group): (x1 * x2 = y1 * y2) <=> (x1/y2 = y1/x2).
proof strict.
  rewrite -(pow_log x1) -(pow_log x2) -(pow_log y1) -(pow_log y2).
  rewrite -!div_def !log_pow !mul_pow -!pow_bij;split => Heq;
  ringeq Heq.
qed.

lemma log_mul (x y:group): log (x * y) = log x + log y.
proof strict.
  by rewrite -{1}(pow_log x) -{1}(pow_log y) mul_pow log_pow.
qed.

lemma log_powx (x:group) (p:F.t): log (x^p) = log x * p.
proof strict.
  by rewrite -{1}(pow_log x) pow_pow log_pow.
qed.

lemma log_opp (x:group): log (-x) = -log x.
proof strict.
  by rewrite -{1}(pow_log x) -pow_opp log_pow.
qed.

lemma div_pow (x y:group) (p:F.t): x ^ p / y ^ p = (x/y)^p.
proof strict.
  rewrite -!div_def log_powx (log_powx y) pow_pow;congr => //;ringeq.
qed.

lemma pow_mul_log (a b c d:group) (p:F.t): 
   a <> c => 
   a^p * b = c^p * d =>
   p = log (d/b) / log(a/c).
proof strict.
  intros Hab.
  rewrite eq_sym mulC eq_mul_div=> ->.
  rewrite div_pow log_powx -div_def log_pow;fieldeq.
  generalize Hab;rewrite -!not_def => H1 H2;apply H1.
  rewrite log_bij;ringeq => //.  
qed.

require import Monoid.
import Int.
clone Comoid as Gp with
  type Base.t   <- group,
  op Base.Z     <- g1, 
  op Base.( + ) <- CG.( * )
  proof Base.* by smt.

op prodi = Gp.sum_ij.  

lemma prodi_eq i j f1 f2 : 
  (forall k, i <= k < j => f1 k = f2 k) => 
  prodi i (j-1) f1 = prodi i (j-1) f2.
proof.
  rewrite /prodi /Gp.sum_ij => Hk. 
  apply Gp.sum_eq => x;rewrite FSet.Interval.mem_interval => Hx; apply Hk;smt.
qed.

(* Lifting of operation *)

theory Gfun.

  op ( * ) (f1 f2:'a -> group) = fun a, f1 a * f2 a.
  op [ - ] (f1:'a -> group)    = fun a, -f1 a.
  op ( / ) (f1 f2:'a -> group) = fun a, f1 a / f2 a.
  op ( ^ ) (f1:'a -> group) (f2:'a -> t) = fun a, f1 a ^ f2 a.
  op log  (f1:'a -> group)     = fun a, log (f1 a).
  op ( ** ) (f1 f2:'a -> group) = [+-]g ^ (log f1 * log f2).
  op ( ^^ ) (f1:'a -> group) (i:'a -> int) = [+-]g ^ ((log f1)^i). 

  lemma mul_pow g (x y:'a -> t): g ^ x * g ^ y = g ^ (x + y).
  proof.
    apply ExtEq.fun_ext => z;apply (mul_pow (g z) (x z) (y z)).
  qed.

  lemma pow_pow g (x y:'a -> t): (g ^ x) ^ y = g ^ (x * y).
  proof.
    apply ExtEq.fun_ext => z;apply (pow_pow (g z) (x z) (y z)).
  qed.

  lemma pow_mul (g1 g2:'a -> group) x: g1^x * g2^x = (g1*g2)^x.
  proof.
    apply ExtEq.fun_ext => z; apply (CG.pow_mul (g1 z) (g2 z) (x z) ).
  qed.

  lemma pow_opp (x:'a -> group) (p:'a->F.t): x^(-p) = -(x^p).
  proof.
    apply ExtEq.fun_ext => z;apply (pow_opp (x z) (p z)).
  qed.

  lemma prodi_mulD i j (f1 f2:int -> group): 
     prodi i j (f1 * f2) = prodi i j f1 * prodi i j f2.
  proof.
    rewrite /Gfun.( * ) /prodi /Gp.sum_ij;elim /FSet.set_ind (FSet.Interval.interval i j).
      by rewrite !Gp.sum_empty mul1.
    intros x s Hx Hrec;rewrite !Gp.sum_add //= Hrec;ringeq.
  qed.

  lemma prodi_pow_fx i j (f:int -> group) p: prodi i j (f ^ [+-]p) = prodi i j f ^ p.
  proof strict.
    rewrite /prodi /Gp.sum_ij;elim /FSet.set_ind (FSet.Interval.interval i j);first by smt.
    by intros x s Hx Hr;rewrite !Gp.sum_add //;smt.
  qed.

  lemma prodi_pow_xf i j x (f:int -> t): prodi i j (([+-]x) ^ f) = x ^ Fs.sum_ij i j f.
  proof strict.
    rewrite /prodi /Gp.sum_ij /Fs.sum_ij;elim /FSet.set_ind (FSet.Interval.interval i j).
      rewrite Gp.sum_empty Fs.sum_empty -(pow_log x); smt.
    intros k s Hk Hr;rewrite Gp.sum_add // Fs.sum_add // Hr;smt.
  qed.

  lemma prodi_inv i j (f:int -> group): prodi i j ([-]f) = [-](prodi i j f).
  proof strict.
    rewrite /prodi /Gp.sum_ij;elim /FSet.set_ind (FSet.Interval.interval i j);first by smt.
    intros x s Hx Hr;rewrite !Gp.sum_add // Hr /Gfun.([-]);ringeq.
  qed.

end Gfun.
export Gfun.

end CG.