From mathcomp Require Import all_ssreflect all_algebra.
Require Import tactics binomialz bigopz arithmetics seq_defs a_props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.


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
  0 <= k -> 1 <= m -> m < k + 1 -> k < Posz n + 1 ->
  c n k * d n k m =
  ((-1) ^ (m + 1) / 2%:Q) / (m%:Q ^ 3 * (binomialz k m)%:Q ^ 2) *
  (binomialz n k * binomialz (Posz n + k) k *
  binomialz (Posz n - m) (Posz n - k) * binomialz ((Posz n) + k) (k - m))%:Q.
Proof.
case: m k => m // [] // k _ h1m.
rewrite /c /d -!PoszD !addn1 !ltz_nat !ltnS !rmorphM /= => hmk hkn.
have hnm : (m <= n)%N by lia.
rewrite (subzn hkn) (subzn hmk) (subzn hnm) !binzE; [| lia..].
have -> : (n + k - (k - m) = n + m)%N by rewrite subnBA // addnAC addnK.
have -> : (n - m - (n - k) = k - m)%N by rewrite subnAC subnBA // addKn.
rewrite !addnK; field.
rewrite !pnatr_eq0 -!lt0n !fact_gt0; lia.
Qed.

(* First significant step in the proof: for any n, the rational number *)
(* 2 * (l n) * (b n) is in fact an integer *)


(* Notice that any rational number becomes an integer when multiplied *)
(* by (iter_lcm n) for n large enough. *)
(* This lemma is not in arithmetics.v becuse it uses type rat. *)

Lemma iter_lcmn_mul_rat (r : rat) (n : nat) : `|denq r| <= n ->
  (iter_lcmn n)%:Q * r \is a Num.int.
Proof.
move=> ledn; rewrite -[r]divq_num_den mulrA -rmorphM.
by apply/Qint_dvdz/dvdz_mulr/iter_lcmn_div; rewrite // absz_gt0 denq_neq0.
Qed.


(* FIXME : still too much nat/int conversions, not so easy to do better *)
Lemma Qint_l3b (n : nat) : 2%:Q * (l n)%:Q ^ 3 * b (Posz n) \is a Num.int.
Proof.
set goal_term := (X in X \is a Num.int).
have {goal_term} -> : goal_term =
  2%:Q * (l n)%:Q ^ 3 * ghn3 n * a n +
  2%:Q * (l n)%:Q ^ 3 * (\sum_(0 <= k < Posz n + 1 :> int) c n k * s n k).
  rewrite -mulrA -mulrDr mulr_sumr -big_split /=; congr (_ * _).
  by apply: eq_bigr => i _; rewrite mulrC -mulrDr.
rewrite mulr_sumr big_int_cond /=.
apply/rpredD/rpred_sum.
  apply/rpredM/Qint_a; rewrite mulr_sumr big_int_cond; apply: rpred_sum.
  move=> i /andP [/andP [h1i hin] _]; rewrite -mulrA expfV -expfzMl.
  apply/rpredM/rpredX/iter_lcmn_mul_rat; rewrite // normr_denq denqVz; lia.
move=> k /andP [/andP [le0k lekn] _]; rewrite mulrA mulr_sumr big_int_cond /=.
apply/rpred_sum => m /andP [/andP [le1m lemk] _]; rewrite -mulrA cdM //.
pose hardest_term := (l n)%:Q ^ 3 / (m%:Q ^ 3 * (binomialz k m)%:Q ^ 2).
set other_term := (X in _ * _ * _ * X).
set goal_term := (X in X \is a Num.int).
have {goal_term} -> : goal_term = (-1) ^ (m + 1) * other_term * hardest_term.
  rewrite /goal_term /hardest_term; field.
  rewrite !intr_eq0 lt0r_neq0 ?binz_gt0; lia.
apply/rpredM; first by rewrite expN1r rpred_zify.
have {hardest_term other_term} -> :
    hardest_term = ((l n)%:Q / m%:Q) * ((l n)%:Q / (m * binomialz k m)%:Q) ^ 2.
  rewrite expfzMl {}/hardest_term; field.
  by rewrite !intr_eq0 lt0r_neq0 ?binz_gt0; lia.
apply/rpredM/rpredX.
  apply: iter_lcmn_mul_rat; rewrite normr_denq denqVz; lia.
case: k m le0k le1m lemk lekn => [] k [] m // *.
rewrite binz_nat_nat; apply/Qint_dvdz/dvd_nbin_iter_lcmn; lia.
Qed.
