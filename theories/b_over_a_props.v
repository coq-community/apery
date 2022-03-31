Require Import BinInt.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import extra_mathcomp field_tactics lia_tactics shift.
Require annotated_recs_c.
Require Import seq_defs initial_conds algo_closures reduce_order a_props.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(**** We introduce and study the casoratian of a and b ****)

(* Definition of the sequence: reminder of a a 2x2 wronskian *)
Definition ba_casoratian (k : int) : rat :=
  (b (int.shift 1 k) * a k) - b k * a (int.shift 1 k).

(* This is the bulk of section 5 in apery1.html, and equation (7) p.5 in
  Van der Poorten's paper (not true for n = 1) *)

Lemma ba_casoratianE (n : int) :
  2%:~R <= n -> ba_casoratian n = 6%:Q / (n%:Q + 1) ^ 3.
Proof.
move=> le2n; have le0n : 0 <= n by exact: le_trans le2n.
pose v (k : int) : rat := 6%:Q / (k%:Q + 1) ^ 3.
pose c1 := annotated_recs_c.P_cf2.
pose c0 := annotated_recs_c.P_cf0.
pose Urec (v : int -> rat) := forall (k : int), 2%:~R <= k ->
                      c1 k * v (int.shift 1 k) - c0 k * v k = 0.
have uUrec : Urec ba_casoratian.
  move=> k le2k; have le0k : 0 <= k by exact: le_trans le2k.
  have brec := b_Sn2 le0k; have arec := a_Sn2 le2k.
  have -> : 0 = a (int.shift 1 k) * annotated_recs_c.P_horner b k
                - b (int.shift 1 k) * annotated_recs_c.P_horner a k.
    by rewrite brec arec !mulr0 subrr.
  rewrite /annotated_recs_c.P_horner /annotated_recs_c.P_seq /c1 /c0.
  by rewrite /punk.horner_seqop /= /ba_casoratian; rat_field.
have vUrec : Urec v.
  move=> k le2k.
  rewrite /c0 /c1 /annotated_recs_c.P_cf2 /annotated_recs_c.P_cf0 /v.
  by rewrite int.shift2R; rat_field; rewrite {}/emb; goal_to_lia; intlia.
(* this step below is only the fact that U is a rec of order 1 : should be *)
(* obtained from something more general... *)
suff {uUrec vUrec v} Urec1P (w1 w2 : int -> rat) : w1 2 = w2 2 ->
  Urec w1 -> Urec w2 -> forall (k : int), 2%:~R <= k -> w1 k = w2 k.
  apply: (Urec1P _ v) => //; rewrite /ba_casoratian /v b2_eq b3_eq.
  rewrite int.shift2Z a2_eq a3_eq.
  rat_field; do 2! (split; first by move/eqP; rewrite rat_of_Z_eq0).
  by move/eqP; rewrite rat_of_Z_eq0.
have hUrec w k : Urec w -> 2%:~R <= k -> w (int.shift 1 k) = (c0 k / c1 k) * w k.
  move=> wUrec le2k; rewrite mulrAC; apply: canRL (mulfK _) _.
    rewrite /c1 /annotated_recs_c.P_cf2 expf_eq0 /= rat_of_ZEdef.
    rewrite  -[rat_of_Z_ 2]/(2%:Q) -rmorphD /= intr_eq0; intlia.
  by apply/eqP; rewrite [_ * c1 k]mulrC -subr_eq0 wUrec.
move=> ic Uw1 Uw2 [] //; elim => // [[]] // [] // k ihk _.
by rewrite -[_.+3]addn1 PoszD -int.zshiftP !hUrec // ihk.
Qed.


(* A technical (trivial) fact to be used in the proof creal_bovera_seq *)
(* that b / a is Cauchy convergent. *)
Fact lt_0_ba_casoratian (n : nat) : 0 < 6%:Q / (n%:Q + 1%:Q) ^ 3.
Proof. by apply/divr_gt0/exprn_gt0 => //; rewrite -rmorphD ltr0n addn1. Qed.


(**** We now define and study the sequence b n / a n ****)

Definition b_over_a_seq (k : int) := b k / a k.


(* The difference of two terms of b n / and has this nice shape *)
(* due to the previous results on the casoratian. *)
Lemma Db_over_a_casoratian (i j : nat) : (2 <= j)%N -> (j <= i)%N ->
  b_over_a_seq i - b_over_a_seq j =
  \sum_(j <= k < i) 6%:Q / (k%:Q + 1) ^ 3 / (a (int.shift 1 k) * a k).
Proof.
move=> le2j leji; rewrite -(telescope_nat (fun k => b_over_a_seq (Posz k))) //.
rewrite [RHS]big_nat_cond [LHS]big_nat_cond.
apply: eq_bigr => k /andP[/andP[lejk ltki] _].
rewrite -ba_casoratianE /b_over_a_seq /ba_casoratian.
  by rewrite PoszD int.zshiftP; rat_field; split; apply/eqP; apply: a_neq0.
by rewrite lez_nat; apply: leq_trans lejk.
Qed.
