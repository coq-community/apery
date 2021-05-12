From mathcomp Require Import all_ssreflect all_algebra.

Require Import extra_mathcomp.

Require Import binomialz bigopz lia_tactics field_tactics.
Require Import harmonic_numbers seq_defs.

Require Import arithmetics a_props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope ring_scope.


(**** Properties the sequence b ****)

(* We introduce the sequence lcm(1..n) and use the same notation (l n) as *)
(* in the companion paper : l n is lcm(1..n) *)
Local Notation l := iter_lcmn.


(* A technical lemma expressing the product of c and d as a power of index and *)
(* binomial coefficients, to be used in the proof of the integrality *)
(* lemma Qint_l3b. Cf section 2 of apery1.html for a readable version...*)
(* This should be a trivial normalization of rational functions but we *)
(* need to fiddle with nat/int conversion because the factorial is only *)
(* defined on nats for the time being (quite ugly actually). *)
(* The parentheses matter to ease subterm selection in the proof of Qint_l3b *)

Fact cdM (n : nat) (k m : int) :
  0 <= k -> 1 <= m -> m < k + 1 -> k < (Posz n) + 1 ->
  c n k * d n k m =
  ((-1) ^ (m + 1) / 2%:~R) * (m%:~R ^ 3 * (binomialz k m) ^ 2)^-1 *
  ((binomialz n k) * (binomialz (Posz n + k) k) *
  (binomialz (Posz n - m)) (Posz n - k) * (binomialz ((Posz n) + k) (k - m))).
move=> h0k h1m hmk hkn; rewrite /c /d.
case: m h1m hmk => // m; case: k h0k hkn => k _ //.
rewrite -![_ + 1]PoszD !ltz_nat (addn1 n) (addn1 k) !ltnS => hkn h1m hmk.
have hnm : (m <= n)%N by apply: leq_trans hkn.
rewrite (subzn hkn) (subzn hmk) (subzn hnm) !binzE // ?leq_addr ?leq_addl //; last first.
- by apply: leq_sub2l.
- apply: leq_trans (leq_subr _ _) _ ; exact: leq_addl.
have -> : (n + k - (k - m) = n + m)%N by rewrite subnBA // addnAC addnK.
have -> : (n - m - (n - k) = k - m)%N.
  rewrite -subnDA addnBA // subnBA addnC ?subnDr //; apply: leq_trans hkn _.
  by exact: leq_addr.
rewrite !addnK [Posz (m + 1)]PoszD. 
rat_field.
rewrite {}/emb7 {}/emb4 {}/emb0 {}/emb3 {}/emb6{} /emb1 {}/emb {}/emb5 {emb2}.
do 8! (split; first by apply/eqP; rewrite intr_eq0 -lt0n // ?fact_gt0).
by apply/eqP; rewrite intr_eq0 -lt0n // ?fact_gt0.
Qed.

(* First significant step in the proof: for any n, the rational number *)
(* 2 * (l n) * (b n) is in fact an integer *)


(* Notice that any rational number becomes an integer when multiplied *)
(* by (iter_lcm n) for n large enough. *)
(* This lemma is not in arithmetics.v becuse it uses type rat. *)

Lemma iter_lcmn_mul_rat (r : rat) (n : nat) : `|denq r| <= n ->
  ((iter_lcmn n)%:~R * r)%R \is a Qint.
Proof.
move=> ledn; rewrite -[r]divq_num_den mulrA -rmorphM; apply: Qint_dvdz.
apply: dvdz_mulr; rewrite dvdzE /=; apply: iter_lcmn_div => //.
rewrite absz_gt0; exact: denq_neq0.
Qed.


(* FIXME : still too much nat/int conversions, not so easy to do better *)
Lemma Qint_l3b (n : nat) : 2%:~R * ((l n)%:~R ^ 3) * (b (Posz n)) \is a Qint.
Proof.
set goal_term := (X in X \is a Qint).
have {goal_term} -> : goal_term =
  2%:~R * (l n)%:~R ^ 3 * ghn3 n * a n +
  2%:~R * (l n)%:~R ^ 3 * (\sum_(0 <= k < Posz n + 1 :> int) c n k * s n k).
  rewrite -mulrA -mulrDr mulr_sumr -big_split /= /goal_term; rewrite /b.
  by congr (_ * _); apply: eq_bigr => i _; rewrite /v /u mulrDr mulrC.
have left_arg_is_int : 2%:~R * (l n)%:~R ^ 3 * ghn3 n * a n \is a Qint.
  apply: rpredM; last exact: Qint_a.
  rewrite -[2%:~R * _ * _]mulrA; apply: rpredM => //.
  suff h i : (1 <= i < Posz n + 1) -> (l n)%:~R ^ 3 / i%:~R ^ 3 \is a Qint.
    rewrite /ghn3 /ghn mulr_sumr big_int_cond; apply: rpred_sum => i.
    by rewrite andbT; exact: h.
  case/andP=> h1i hin; rewrite expfV -expfzMl; apply: rpredX.
  by apply: iter_lcmn_mul_rat; rewrite normr_denq denqVz ?gtr0_norm; intlia.
suff {left_arg_is_int} right_arg_is_int :
     2%:~R * (l n)%:~R ^ 3 * (\sum_(0 <= k < Posz n + 1 :> int) c n k * s n k)
         \is a Qint by exact: rpredD.
suff sumd_is_int (k m : int) : 0 <= k -> 1 <= m -> m < k + 1 -> k < Posz n + 1 ->
   2%:~R * (l n)%:~R ^ 3 * c n k * d n k m \is a Qint.
  rewrite mulr_sumr big_int_cond /=.
  apply: rpred_sum => k; rewrite andbT => /andP [le0k lekn].
  rewrite /s mulrA mulr_sumr big_int_cond /=.
  apply: rpred_sum => m; rewrite andbT => /andP [le0m lemi]; exact: sumd_is_int.
move=> le0k le1m lemk lekn.
pose hardest_term :=  (l n)%:~R ^ 3 / (m%:~R ^ 3 * binomialz k m ^ 2).
suff h : hardest_term \is a Qint.
(* Without the  pattern, rewrite cfM now diverges!!! *)
rewrite -mulrA [X in _ * _ * X]cdM //. set other_term := (X in _ * _ * _ * X).
  set goal_term := (X in X \is a Qint).
  have {goal_term} -> : goal_term = (-1) ^ (m + 1) * other_term * hardest_term.
    rewrite {}/goal_term /hardest_term; rat_field.
    split; first by apply/eqP; apply: lt0r_neq0; apply: binz_gt0; intlia.
    by split => //; apply/ eqP; rewrite intr_eq0; intlia.
  apply: rpredM => //; apply: rpredM; first by rewrite expN1r; exact: rpredX.
  rewrite {}/other_term.
  by do 4! ((try apply: rpredM); last by apply: Qint_binomialz; intlia).
have {hardest_term} -> : hardest_term =
  ((l n)%:~R / m%:~R) * ((l n)%:~R / (m%:~R * binomialz k m)) ^ 2.
  rewrite expfzMl {}/hardest_term; rat_field.
  split; first by apply/eqP; apply: lt0r_neq0; apply: binz_gt0; intlia.
  by apply/eqP; rewrite intr_eq0; intlia.
apply: rpredM.
- by apply: iter_lcmn_mul_rat; rewrite normr_denq denqVz ?gtr0_norm; intlia.
apply: rpredX; case: k le0k lemk lekn => k // ; case: m le1m => m //.
rewrite -![_ + 1]PoszD !ltz_nat !addn1 => *.
by rewrite binz_nat_nat -rmorphM /=; apply: Qint_dvdz; apply: dvd_nbin_iter_lcmn.
Qed.
