From mathcomp Require Import all_ssreflect all_algebra.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

(******************************************************************************)
(* The main purpose of this library is to establish properties of the         *)
(* sequence lcm(1..n). The proof of irrationality that we formalize           *)
(* relies on lemma 'dvdnbinD' proved in the present file, which               *)
(* states a strong divisibility property between binomial coefficients and    *)
(* lcm(1..n).                                                                 *)
(* This file defines:                                                         *)
(* iter_lcmn n   == the least common multiple of the n-th first natural       *)
(*                  numbers                                                   *)
(* log_floor p n == the largest power of p that is smaller or equal to n      *)
(******************************************************************************)

Section ExtraBigOp.

Local Open Scope nat_scope.

Lemma logn_prod (I : Type) (r : seq I) F p : (forall i : I, 0 < F i) ->
  logn p (\prod_(i <- r) F i) = \sum_(i <- r) logn p (F i).
Proof.
move => H; elim: r => [|a l Hl]; first by rewrite !big_nil logn1.
rewrite !big_cons lognM ?Hl //; exact: prodn_gt0.
Qed.


Lemma natsumrB A (P : A -> bool) F1 F2 l :
  (forall i, (P i -> F1 i >= F2 i)) ->
  \sum_(i <- l | P i) F1 i - \sum_(i <- l | P i) F2 i =
  \sum_(i <- l | P i) (F1 i - F2 i).
Proof.
move => Hge; elim: l => [|a l Hl]; first by rewrite !big_nil.
case HPa : (P a); rewrite !big_cons HPa /=; last exact: Hl.
have H12 : F1 a = F2 a + (F1 a - F2 a) by rewrite subnKC //; exact: (Hge a HPa).
rewrite H12 -addnA subnDl -addnBA; last by apply: leq_sum.
by rewrite Hl -H12.
Qed.

Lemma sum_ord_const_nat n m : \sum_(i < n) m = m * n.
Proof. by rewrite big_const_ord iter_addn_0. Qed.

Lemma sum1_ord n : \sum_(j < n) 1 = n.
Proof. by rewrite sum_ord_const_nat mul1n. Qed.

Lemma prod_ord_const n m : \prod_(i < n) m = m ^ n.
Proof. by rewrite big_const_ord iter_muln_1. Qed.

Lemma leq_prodn I r (P : pred I) F1 F2 :
  (forall i, P i -> F1 i <= F2 i) ->
   \prod_(i <- r | P i) F1 i <= \prod_(i <- r | P i) F2 i.
Proof.
move=> leF; elim: r => [| x r ihr] /=; first by rewrite !big_nil.
rewrite !big_cons; case: ifP => hPx //; apply: leq_mul => //; exact: leF.
Qed.

End ExtraBigOp.

(**** Some extra results about (the factorial of) the p-valuation of a ****)
(**** natural number, implemented by (logn p n) with p prime.          ****)

Lemma fact_logp_sum p n : prime p -> logn p n`! = \sum_(i < n) (n %/ p ^ i.+1).
Proof.
elim: n => [|n ihn] p_prime; first by rewrite fact0 logn1 big_ord0.
rewrite factS lognM ?fact_gt0 // big_ord_recr /= ihn //=.
rewrite divn_small ?addn0; last by rewrite ltn_expl ?prime_gt1.
have -> : logn p n.+1 = \sum_(i < n) (p ^ i.+1 %| n.+1).
  rewrite -big_mkcond sum1dep_card; set P := [set x | _].
  have -> : P = [set i : 'I__ | i.+1 <= logn p n.+1].
    apply/setP => i; rewrite !inE /= -{1}(@partnC p n.+1) //.
    rewrite Gauss_dvdl; first by rewrite p_part dvdn_Pexp2l ?prime_gt1.
    by rewrite (@pnat_coprime p) ?part_pnat ?pnat_exp ?pnat_id.
  rewrite -sum1dep_card big_ord_narrow ?sum_nat_const ?muln1 ?card_ord //.
  rewrite -(@leq_exp2l p) ?prime_gt1 // -p_part.
  by rewrite (leq_trans (dvdn_leq _ (dvdn_part p _))) // ltn_expl ?prime_gt1.
rewrite -big_split; apply: eq_big => //= i _; set q := p ^ i.+1; symmetry.
have q_gt0 : 0 < q by rewrite ?expn_gt0 ?prime_gt0.
rewrite {1}(divn_eq n q) -addn1 -addnA divnMDl // addnC addn1.
have -> // : (q %| n.+1) = ((n %% q).+1 == q).
  rewrite -{3}[q]prednK // eqSS.
  by rewrite -(@modn_small q.-1 q) -1?(@eqn_modDr 1) ?addn1 prednK // modnn.
have [->|hi] := altP eqP; first by rewrite divnn q_gt0.
by rewrite divn_small // ltn_neqAle hi ltn_mod.
Qed.

(* Same as fact_logp_sum, with a wider range for the sum. *)
Lemma fact_logp_sum_widen p m n : prime p -> (m >= n)%N ->
  logn p n`! =  \sum_(i < m) (n %/ p ^ i.+1).
move => prime_p leq_nm; rewrite logn_fact //; symmetry.
(* FIXME : here I would like to simply 'rewrite big_mkord', but I need *)
(* to specify both the (dummy) predicate and the summand... *)
pose G (i : nat) := n %/ p ^ i.+1.
rewrite -[LHS](big_mkord (fun _ => true) G); rewrite {}/G.
rewrite (big_cat_nat _ _ _ (leq0n n) leq_nm) /= addnC.
rewrite big_nat_cond /= big1; first by rewrite add0n big_add1.
move=> i; rewrite andbT => /andP [leni ltim]; apply: divn_small.
apply: leq_trans (ltn_expl _ _); first exact: leq_trans leni _.
exact: prime_gt1.
Qed.

(* Yet an other variant of fact_logp_sum. *)
Lemma fact_logp_sum_small p j n : prime p -> (n < p ^ j.+1) ->
  logn p n`! =  \sum_(i < j) (n %/ p ^ i.+1).
Proof.
move => prime_p leq_npj.
case: (ltnP j n) => [le_jn|lt_nj]; last by rewrite (@fact_logp_sum_widen p j).
rewrite logn_fact //. have hl : 1 <= j.+1 by [].
have hr : j.+1 <= n.+1 by exact: ltnW.
rewrite (big_cat_nat _ _ _ hl hr) /= addnC big_nat_cond /= big1.
  by rewrite add0n big_add1 /= big_mkord.
move=> i; rewrite andbT => /andP [leni ltim]; apply: divn_small.
apply: leq_trans leq_npj _; rewrite leq_exp2l //; exact: prime_gt1.
Qed.

(**** Definition and some elementary results about lcm(1..n) ****)


(* This is the least common multiple of the n-th first natural numbers *)
Definition iter_lcmn (n : nat) := \big[lcmn/1%N]_(1 <= i < n.+1) i.

(* We use the same notation as in the paper. *)
Local Notation l := iter_lcmn.

Lemma iter_lcmn0 : iter_lcmn 0 = 1.
Proof. by rewrite /iter_lcmn big_geq. Qed.

Lemma iter_lcmnS m : iter_lcmn m.+1 = lcmn (iter_lcmn m) m.+1.
Proof. by rewrite /iter_lcmn 2!big_add1 big_nat_recr /=. Qed.

Fact iter_lcmn_gt0 (n : nat) : (l n > 0)%N.
Proof.
elim: n => [|n ihn]; first by rewrite iter_lcmn0.
by rewrite /iter_lcmn (@big_cat_nat _ _ _ n.+1) //= lcmn_gt0 ihn big_nat1.
Qed.

Fact iter_lcmn_leq_div (n m : nat) : (n <= m)%N -> l n %| l m.
Proof.
move=> ?; rewrite /iter_lcmn [X in _ %| X](@big_cat_nat _ _ _ n.+1) //.
exact: dvdn_lcml.
Qed.

Fact iter_lcmn_div (n m : nat) : (0 < n)%N -> (n <= m)%N -> n %| l m.
Proof.
move=> lt0n lenm; apply: dvdn_trans (iter_lcmn_leq_div lenm); rewrite /iter_lcmn.
rewrite (@big_cat_nat _ _ _ n) //= big_nat1; exact: dvdn_lcmr.
Qed.

(* (trunc_log p) is greater than (logn p) in the following sense: *)
Lemma  leq_logn_trunc p m k : (1 < p)%N -> (m <= k)%N ->
                              (logn p m <= trunc_log p k)%N.
Proof.
case: m => [|m]; rewrite ?logn0 //.
move=> h1p leq_mk; apply: trunc_log_max=> //; apply: leq_trans leq_mk.
by rewrite -p_part dvdn_leq // dvdn_part.
Qed.

(* (logn p n!) can be expressed as a sum of trunc_log *)
Lemma logp_sum_floor p n : prime p ->
 logn p (n`!) =  \sum_(i < trunc_log p n) (n %/ p ^ i.+1).
Proof.
move=> hp; rewrite -fact_logp_sum_small //; apply: trunc_log_ltn.
exact:  prime_gt1.
Qed.

(**** p-Valuations of binomial coefficients ****)
Lemma logn_divz p a b : (0 < a)%N -> b %| a ->
  ((logn p (a %/ b))%:Z = (logn p a)%:Z - (logn p b)%:Z)%R.
Proof. by move=> ? ?; rewrite logn_div // -subzn // dvdn_leq_log.
Qed.

Lemma bin_valp m k p : (m > 0) -> prime p -> (m <= k) ->
                       (logn p (m * 'C(k, m)) <= logn p (l k)).
Proof.
move => gt_m_0 prime_p leq_mk.
have hp2 : (p >= 2) by exact: prime_gt1.
have gt_k0 : (k > 0) by rewrite (@leq_trans m).
have -> : logn p (m * 'C(k, m)) =
          (logn p m + (logn p k`! - (logn p m`! + logn p (k - m)`!)%N)).
  rewrite lognM ?bin_gt0 // bin_factd // logn_div // ?lognM ?fact_gt0 // .
  by rewrite -(bin_fact leq_mk) dvdn_mull.
have : trunc_log p k <= logn p (l k).
  rewrite - pfactor_dvdn ?d_lt0 // ; last by apply: iter_lcmn_gt0.
  by apply: iter_lcmn_div; [by rewrite expn_gt0 ltnW | exact: trunc_logP].
apply: leq_trans.
set lhs := (X in X <= _).
have Hi : forall i : 'I_(logn p m),
  m %/ p ^ i.+1 + (k - m) %/ p ^ i.+1 <= k %/ p ^ i.+1.
  move => [i] Hi /= .
  rewrite -divnDl ?subnKC // pfactor_dvdn // .
have hsplit : trunc_log p k = (logn p m) + ((trunc_log p k) - (logn p m)).
  by rewrite subnKC //; exact: (leq_logn_trunc _ _).
have {lhs} -> : lhs = logn p m +
    (\sum_(i < trunc_log p k - logn p m)
       (k %/ p ^ (logn p m + i).+1) -
    \sum_(i < trunc_log p k - logn p m) (m %/ p ^ (logn p m + i).+1 +
                                        (k - m) %/ p ^ (logn p m + i).+1)%N).
  rewrite /lhs logp_sum_floor // !(@fact_logp_sum_small p (trunc_log p k)) //; first last.
  - by apply: (leq_ltn_trans leq_mk); apply: trunc_log_ltn.
  - by apply  (leq_ltn_trans (leq_subr m k) (trunc_log_ltn k hp2)).
  rewrite -!big_split /=;congr (_ + _).
  rewrite [in LHS]hsplit /=. rewrite 2!big_split_ord /= .
  have -> : \sum_(i < logn p m) (m %/ p ^ i.+1 + (k - m) %/ p ^ i.+1) =
            \sum_(i < logn p m) k %/ p ^ i.+1.
    by apply: eq_bigr => [] [i] Him _ /= ; rewrite -divnDl ?subnKC ?pfactor_dvdn.
  by rewrite subnDl.

suff Hle : (\sum_(i < trunc_log p k - logn p m) k %/ p ^ (logn p m + i).+1 -
    \sum_(i < trunc_log p k - logn p m)
       (m %/ p ^ (logn p m + i).+1 + (k - m) %/ p ^ (logn p m + i).+1)) <=
       (trunc_log p k - logn p m).
  by rewrite  [in X in _ <= X]hsplit leq_add.
suff Heq1 : trunc_log p k - logn p m = \sum_(i < (trunc_log p k) - logn p m) 1.
  rewrite leq_subLR [in X in _ <= _ + X]Heq1 -big_split /= leq_sum // => i _.
  have Hk : k = m + (k - m) by rewrite subnKC.
  by rewrite [in X in X %/ _ <= _]Hk; rewrite leq_divDl.
by rewrite sum1_card card_ord.
Qed.

(* In the proof that zeta(3) is irrational, we use this corollary to show *)
(* that (lcn (1..n))^3 * b_n is an integer. *)
Corollary dvd_nbin_iter_lcmn (i j : nat) (n : nat) :
  (1 <= j) -> (j  <= i) -> (i <= n) -> (j * 'C(i, j) %| l n).
Proof.
move=> le0j leji lein.
apply/dvdn_partP => [|p hp]; first by rewrite muln_gt0 bin_gt0 le0j.
apply: dvdn_trans ( iter_lcmn_leq_div lein); move: hp.
rewrite mem_primes; case/and3P=> pp hpos hdvd.
rewrite p_part pfactor_dvdn //; last first.
  by apply: iter_lcmn_gt0; apply: leq_trans leji.
exact: bin_valp.
Qed.
