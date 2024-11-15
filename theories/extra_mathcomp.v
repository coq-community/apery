From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint rat all_field.
From mathcomp Require Import bigenough.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory BigEnough.

Section ExtraBinomial.

Lemma ffact_le_expn m p : p ^_ m <= p ^ m.
Proof.
elim: m p => [|m IHm] p //.
by rewrite ffactnSr expnSr; apply/leq_mul/leq_subr/IHm.
Qed.

End ExtraBinomial.

Section ExtraPrime.

Lemma lognn p (Hp : prime p) : logn p p = 1.
Proof. exact: pfactorK 1 Hp. Qed.

Lemma partp_dvdn p (Hprime : prime p) n m :
  (0 < n) -> (p ^ m %| n) -> p ^ m %| n`_p .
Proof. by move => Hn Hdiv; rewrite -(pfactorK m Hprime) -p_part partn_dvd. Qed.

Lemma trunc_logn0 n : trunc_log n 0%N = 0%N. Proof. by case: n => // [] []. Qed.

(* See also inlined stuff in proof of Lemma 2. *)

End ExtraPrime.

Local Open Scope ring_scope.

Section ExtraSsrNum.

Implicit Types (R : numDomainType) (F : numFieldType).

Lemma ltr_neq R (x y : R) : x < y -> x != y.
Proof. by case: comparableP. Qed.

Lemma ltr_pmul_le_l R (x1 y1 x2 y2 : R) :
   0 < x1 -> 0 < x2 -> x1 <= y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Proof.
rewrite le_eqVlt => posx1 posx2 /predU1P[<-|lt1] lt2.
  by rewrite ltr_pM2l.
by apply: ltr_pM=> //; exact: ltW.
Qed.

Lemma ltr_pmul_le_r R (x1 y1 x2 y2 : R) :
   0 < x1 -> 0 < x2 -> x1 < y1 -> x2 <= y2 -> x1 * x2 < y1 * y2.
Proof.
move=> Hx1 Hx2 Hx1y1 Hx2y2; rewrite mulrC [y1*y2]mulrC; exact: ltr_pmul_le_l.
Qed.

Lemma exp_incr_expp R (x : R) (H1x : 1 <= x) (m n : nat) :
  (m <= n)%N -> x ^+ m <= x ^+ n.
Proof.
move/subnK => <-; rewrite exprD.
exact/ler_peMl/exprn_ege1/H1x/exprn_ge0/le_trans/H1x.
Qed.

Lemma exp_incr_expn R (x : R) (H1x : 0 < x < 1) (m n : nat) :
  (n <= m)%N -> x ^+ m <= x ^+ n.
Proof.
case/andP: H1x => lt0x ltx1 /subnK <-; rewrite exprD.
exact/ler_piMl/exprn_ile1/ltW/ltx1/ltW/lt0x/exprn_ge0/ltW.
Qed.

Lemma ler1q F x: (1 <= ratr x :> F) = (1 <= x).
Proof. by rewrite (_ : 1 = ratr 1) ?ler_rat ?rmorph1. Qed.

Lemma lerq1 F x: (ratr x <= 1 :> F) = (x <= 1).
Proof. by rewrite (_ : 1 = ratr 1) ?ler_rat ?rmorph1. Qed.

Lemma ltrq1 F x: (ratr x < 1 :> F) = (x < 1).
Proof. by rewrite (_ : 1 = ratr 1) ?ltr_rat ?rmorph1. Qed.

Lemma ltr1q F x: (1 < ratr x :> F) = (1 < x).
Proof. by rewrite (_ : 1 = ratr 1) ?ltr_rat ?rmorph1. Qed.

End ExtraSsrNum.

Section ExtraAlgC.

Implicit Types x y z : algC.

Lemma root_le_x (n : nat) x y :
  (0 < n)%N -> 0 <= x -> 0 <= y -> (n.-root x <= y) = (x <= y ^+ n).
Proof.
by move => Hn Hx Hy; rewrite -(ler_pXn2r Hn) ?rootCK // nnegrE rootC_ge0.
Qed.

Lemma root_x_le (n : nat) x y :
  (0 < n)%N -> 0 <= x -> 0 <= y -> (x <= n.-root y) = (x ^+ n <= y).
Proof.
by move => Hn Hx Hy; rewrite -[LHS](ler_pXn2r Hn) ?rootCK // nnegrE rootC_ge0.
Qed.

Lemma root_lt_x (n : nat) x y :
  (0 < n)%N -> 0 <= x -> 0 <= y -> (n.-root x < y) = (x < y ^+ n).
Proof.
by move=> Hn Hx Hy; rewrite -(ltr_pXn2r Hn) ?rootCK // nnegrE rootC_ge0.
Qed.

Lemma root_x_lt (n : nat) x y :
  (0 < n)%N -> 0 <= x -> 0 <= y -> (x < n.-root y) = (x ^+ n < y).
Proof.
by move => Hn Hx Hy; rewrite -[LHS](ltr_pXn2r Hn) ?rootCK // nnegrE rootC_ge0.
Qed.

Lemma rootC_leq (m n : nat) x :
  1 <= x -> (0 < n)%N -> (n <= m)%N -> m.-root x <= n.-root x.
Proof.
move=> Hx Hn Hmn.
have x_ge0 : 0 <= x by apply: le_trans Hx.
rewrite root_le_x -?rootCX ?root_x_le ?exprn_ge0 //; first exact: exp_incr_expp.
by rewrite expr0n; case: eqP.
Qed.

(* Not sure if actually needed in library, but this lemma is helpful
to prove one_plus_invx_expx below *)
Lemma le_mrootn_n (m n : nat) : m.+1.-root n.+1%:R <= n.+1%:R :> algC.
Proof. by rewrite root_le_x ?ler_eXnr // (ler0n, ler1n). Qed.

Lemma prod_root m n x : (0 < m)%N -> (0 < n)%N -> 0 <= x ->
                        (m * n)%N.-root x = m.-root (n.-root x).
Proof.
move => Hm Hn Hx.
have Hmnpos : (0 < m * n)%N by rewrite muln_gt0 Hm Hn.
suff: ((m * n).-root x) ^+ (m*n)%N = (m.-root (n.-root x)) ^+ (m * n)%N.
  by apply: pexpIrn; rewrite // nnegrE ?rootC_ge0 //.
by rewrite rootCK // exprM rootCK // rootCK.
Qed.

End ExtraAlgC.

(*** Two lemmas about geometric sequences. We just use the second one. ***)
Section ExtraGeom.

(* FIXME : these two lemmas are not cleaned up *)
(* The proof uses bigenough so that's not strictly in MathComp, but *)
(* as usual we could eliminate the pose_big_enough a posteriori. *)
Lemma Gseqgt1 (r : rat)(E : rat) : 0 <= E -> 1 < r ->
  exists N : nat, forall n : nat, (N <= n)%N -> E < r ^ n.
Proof.
move=> ge0E lt1r.
pose_big_enough M.
  exists M => k hMk.
  have le1r : 1 <= r by rewrite ltW.
  have {}lt1r : 0 < r - 1 by rewrite subr_gt0.
  suff aux (n : nat) : n%:Q * (r - 1) - 1 <= r ^ n.
    apply: lt_le_trans (aux k); rewrite -ltrBDr opprK -ltr_pdivrMr //.
    have: 0 <= (E + 1) / (r - 1) by apply/divr_ge0/ltW/lt1r/addr_ge0.
    by move/archi_boundP/lt_trans; apply; rewrite ltr_nat.
  rewrite -pmulrn /exprz; elim: n => [|n ihn]; first by rewrite mul0r.
  rewrite mulrSr mulrDl mul1r addrAC -lerBrDr; apply: le_trans ihn _.
  rewrite exprSr -[r - 1]mul1r -[r in _ * r](subrK 1) mulrDr mulr1 addrAC.
  by rewrite -mulrBl lerDr pmulr_lge0 // subr_ge0 exprn_ege1.
by close.
Qed.

Lemma Gseqlt1 (r : rat)(eps : rat) : 0 < eps -> 0 < r < 1 ->
  exists N : nat, forall n : nat, (N <= n)%N -> r ^ n < eps.
Proof.
move=> ge0eps /andP [lt0r ltr1].
have hE : 0 <= eps ^-1 by apply/ltW; rewrite invr_gt0.
have hr : 1 < r ^-1 by rewrite invf_gt1.
have [M hM] := Gseqgt1 hE hr; exists M => n hMn.
rewrite -ltf_pV2 //; first by rewrite invr_expz -exprz_inv; exact: hM.
exact: exprz_gt0.
Qed.

End ExtraGeom.


Section Telescope.

Variable R : zmodType.

Lemma telescope_nat (a b : nat) (f : nat -> R) : (a <= b)%N ->
  \sum_(a <= k < b) (f (k + 1)%N - f k) = f b - f a.
Proof.
rewrite leq_eqVlt => /predU1P[->|]; first by rewrite big_geq // subrr.
case: b => // b; rewrite ltnS => leab.
rewrite big_split sumrN big_nat_recr //= addn1 [_ + f _]addrC big_nat_recl //=.
rewrite opprD addrACA -[RHS]addr0; congr (_ + _).
by rewrite -sumrN -big_split big1 => //= i _; rewrite addn1 subrr.
Qed.

End Telescope.

Section TelescopeProd.

Variable R : fieldType.

Lemma telescope_prod_nat (a b : nat) (f : nat -> R) :
 (forall k, (a <= k < b)%N -> f k != 0) -> (a < b)%N ->
  \prod_(a <= k < b) (f (k + 1)%N / f k) = f b / f a.
Proof.
case: b => // b hf; rewrite ltnS => leab.
rewrite big_split prodfV big_nat_recr //= addn1 [_ * f b.+1]mulrC.
rewrite big_nat_recl //= invfM mulrACA -[RHS]mulr1; congr (_ * _).
rewrite -prodfV -big_split big_nat_cond big1 => //= i /andP[/andP[leai ltib] _].
by rewrite addn1 divff ?hf // ltnS ltib leqW.
Qed.

End TelescopeProd.


Section ExtraZip.

Variables S T : Type.

Lemma zip_nil_l  (t : seq T) : zip [::] t = [::] :> seq (S * T).
Proof. by case: t. Qed.

Lemma zip_nil_r  (s : seq S) : zip s [::] = [::] :> seq (S * T).
Proof. by case: s. Qed.

End ExtraZip.


Section ExtraBigOp.

Lemma big_tuple0 R idx (op : Monoid.law idx) (I : finType) P (F : 0.-tuple I -> R) :
  \big[op/idx]_(t : 0.-tuple I | P t) F t = if P [tuple] then F [tuple] else idx.
Proof.
rewrite big_mkcond (big_pred1 [tuple]) // => x /=; rewrite tuple0 (eqxx [tuple]).
by [].
Qed.

Lemma big_rcons T R idx (op : Monoid.law idx) i r (P : pred T) (F : T -> R) :
    let x := \big[op/idx]_(j <- r | P j) F j in
  \big[op/idx]_(j <- rcons r i | P j) F j = if P i then op x (F i) else x.
Proof.
rewrite -cats1 big_cat /= [in X in op _ X]big_mkcond big_seq1.
by case: ifP=> //; rewrite Monoid.mulm1.
Qed.

End ExtraBigOp.
