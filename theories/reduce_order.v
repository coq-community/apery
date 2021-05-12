Require Import Psatz ZArith.

From mathcomp Require Import all_ssreflect all_algebra.
Require Import binomialz bigopz.
Require Import field_tactics lia_tactics shift.
Require Import extra_mathcomp.
Require Import seq_defs.

Require harmonic_numbers.
Require (* rat_pos *) algo_closures initial_conds.

Require annotated_recs_c.
Require annotated_recs_v.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.


Section ReduceBToOrder2.

Fixpoint b'_rec (n : nat) : rat :=
match n with
| 0 => b 0
| 1 => b 1
| S (S o as o') =>
    let n' := Posz o in
    - (annotated_recs_c.P_cf0 n' * b'_rec o + 
       annotated_recs_c.P_cf1 n' * b'_rec o') /
      annotated_recs_c.P_cf2 n'
end.

Lemma b'_rec_eq (o : nat) (n := Posz o) :
  b'_rec o.+2 =
    - (annotated_recs_c.P_cf0 n * b'_rec o + 
       annotated_recs_c.P_cf1 n * b'_rec o.+1) /
      annotated_recs_c.P_cf2 n.
Proof.  by [].  Qed.

Definition b' (n : int) : rat :=
match n with
| Negz _ => 0
| Posz o => b'_rec o
end.

Lemma b'_Posz (o : nat) : b' (Posz o) = b'_rec o.
Proof.  done.  Qed.

Lemma b'_Sn2_rew (n : int) :
n >= 0 ->
  b' (int.shift 2 n) =
    - (annotated_recs_c.P_cf0 n * b' n + 
       annotated_recs_c.P_cf1 n * b' (int.shift 1 n)) /
      annotated_recs_c.P_cf2 n.
Proof.
case: n => // o _.
rewrite 2!int.shift2Z -2!PoszD.
have -> : (o + 2)%N = o.+2 by rewrite addnC.
have -> : (o + 1)%N = o.+1 by rewrite addnC.
by rewrite b'_Posz b'_rec_eq.
Qed.

Lemma b'0_eq : b' 0 = 0.
Proof.  by rewrite /= initial_conds.b0_eq.  Qed.

Lemma b'1_eq : b' 1 = 6%:~R.
Proof.  by rewrite /= initial_conds.b1_eq.  Qed.

Lemma b'2_eq : b' (2 : int) = rat_of_Z 351 / rat_of_Z 4.
Proof.
rewrite -[Posz 2]/(int.shift 2 0) b'_Sn2_rew // b'0_eq b'1_eq.
rewrite /annotated_recs_c.P_cf0 /annotated_recs_c.P_cf1 /annotated_recs_c.P_cf2.
by apply/eqP; rewrite rat_of_ZEdef; vm_compute.
(* Faster than: rat_field; goal_to_lia; intlia. *)
Qed.

Lemma b'3_eq : b' (3 : int) = rat_of_Z 62531 / rat_of_Z 36.
Proof.
rewrite -[Posz 3]/(int.shift 2 1) b'_Sn2_rew // b'1_eq b'2_eq.
rewrite /annotated_recs_c.P_cf0 /annotated_recs_c.P_cf1 /annotated_recs_c.P_cf2.
(* Doesn't finish: apply/eqP; rewrite rat_of_ZEdef; vm_compute. *)
rat_field.
do 2! (split; first by move/eqP; rewrite rat_of_Z_eq0).
by move/eqP; rewrite rat_of_Z_eq0.
Qed.

Lemma b'4_eq : b' (4 : int) = rat_of_Z 11424695 / rat_of_Z 288.
Proof.
rewrite -[Posz 4]/(int.shift 2 2) b'_Sn2_rew // b'2_eq b'3_eq.
rewrite /annotated_recs_c.P_cf0 /annotated_recs_c.P_cf1 /annotated_recs_c.P_cf2.
rat_field.
do 3! (split; first by move/eqP; rewrite rat_of_Z_eq0).
by move/eqP; rewrite rat_of_Z_eq0.
Qed.

Lemma b'_Sn4 (n : int) : n >= 0 -> annotated_recs_v.P_horner b' n = 0.
Proof.
move=> ?.
rewrite /annotated_recs_v.P_horner /punk.horner_seqop [LHS]/=.
rewrite !b'_Sn2_rew //; [ | intlia ..].
set b'1 := b' _.
set b'2 := b' _.
Fail set b'3 := b' _.
rewrite /annotated_recs_c.P_cf0 /annotated_recs_c.P_cf1 /annotated_recs_c.P_cf2.
rewrite  /annotated_recs_v.P_cf0 /annotated_recs_v.P_cf1.
rewrite /annotated_recs_v.P_cf2 /annotated_recs_v.P_cf3 /annotated_recs_v.P_cf4.
rewrite !rmorphD /=.
rat_field.
goal_to_lia.
intlia.
Qed.

Ltac affine_poly_intlia := 
  rewrite ?rat_of_ZEdef;
  rewrite -1?rmorphM -1?rmorphD -1?rmorphN /=;
  rewrite ?intr_eq0 ?ltr0z ?ler0z; intlia.

Lemma Sn4_flat_to_Sn4_rew (w : int -> rat) :
  (forall n : int, n >= (2 : int) -> annotated_recs_v.P_horner w n = 0) ->
  (forall n : int, n >= (2 : int) ->
    w (int.shift 4 n) =
      - (annotated_recs_v.P_cf0 n * w n + 
         annotated_recs_v.P_cf1 n * w (int.shift 1 n) +
         annotated_recs_v.P_cf2 n * w (int.shift 2 n) +
         annotated_recs_v.P_cf3 n * w (int.shift 3 n)) /
         annotated_recs_v.P_cf4 n).
Proof.
move=> horner_hyp n le_2_n.
have le_0_n : n >= 0 by apply: (le_trans _ le_2_n).
set goal := (_ = _).
move: {horner_hyp} (horner_hyp n le_2_n).
rewrite /annotated_recs_v.P_horner /punk.horner_seqop /=.
set t0 := (X in _ + X = 0).
set t1 := (X in _ + X + t0 = 0).
set t2 := (X in _ + X + t1 + t0 = 0).
set t3 := (X in _ + X + t2 + t1 + t0 = 0).
set t4 := (X in X + t3 + t2 + t1 + t0 = 0).
move=> horner_hyp.
rewrite {}/goal -{1}/t0 -{1}/t1 -{1}/t2 -{1}/t3.
move: @t4 horner_hyp => /=.
set c4 := annotated_recs_v.P_cf4 n => hyp.
clearbody t0 t1 t2 t3.
have c4_neq_0 : c4 != 0.
  rewrite /c4 /annotated_recs_v.P_cf4.
  apply: mulf_neq0; last first.
    apply: expfz_neq0; last by affine_poly_intlia. 
    apply: mulf_neq0; first by affine_poly_intlia. 
    apply: lt0r_neq0; apply: addr_gt0; last exact: rat_of_Z_Zpos.
    apply: addr_gt0; last by affine_poly_intlia.
    apply: addr_gt0; last first.
      apply: mulr_gt0; first by affine_poly_intlia.
      apply: exprz_gt0; affine_poly_intlia.
    apply: addr_gt0.
      apply: mulr_gt0; first by affine_poly_intlia.
      apply: exprz_gt0; affine_poly_intlia.
    apply: mulr_gt0; first by affine_poly_intlia.
    apply: exprz_gt0; affine_poly_intlia.
clearbody c4.  clear le_0_n.
rewrite mulNr.
apply/eqP.
rewrite -addr_eq0.
have <- : (c4 * (w (int.shift 4 n) + (t0 + t1 + t2 + t3) / c4) == 0) =
    (w (int.shift 4 n) + (t0 + t1 + t2 + t3) / c4 == 0).
  by apply: mulrI_eq0; first by apply/lregP.
rewrite mulrDr [c4 * (_ / c4)]mulrC.
rewrite -{}hyp 3!(int.shiftS n).
apply/eqP.  move/eqP in c4_neq_0.
rat_field. 
by done.
Qed.

Lemma shift1_to_plus1 (o : nat) : int.shift 1 (Posz o) = Posz (o.+1).
Proof.  by rewrite /int.shift intS addrC.  Qed.

(* In order to improve modularity wrt to the bound from which we are able to *)
(* establish the recurrence of order 4 for b, we generalize the previous *)
(* version of b'_eq_b which now comes in two steps. The following just says *)
(* that we shift the verification of the initial conditions to the first *)
(* values from which we are able to establish the recurrence by closures. *)
Lemma b'_eq_b_reduction (k : int) :
k >= (2 : int) ->
  b' k = b k -> b' (k + 1) = b (k + 1) ->
  b' (k + 2) = b (k + 2) -> b' (k + 3) = b (k + 3) ->
  forall (n : int), n >= k -> b' n = b n.
Proof.
move=> kpos ebk0 ebk1 ebk2 ebk3 /= n.
(* We would like a usable induction principle on int...*)
(* For now we do the variable change "by hand" in order to call int_rect. *)
pose p : int := n - k; simpl in p.
have -> : n = p + k by rewrite /p addrNK.
clearbody p; clear n.
rewrite ler_addr.
suff gen (n : int) : (0 : int) <= n -> n <= p -> b' (n + k) = b (n + k).
  by move=> p_pos; apply: (gen _ p_pos).
move: n.
elim/int_rect: p => [p h0p hp0 | p ihp n le0n hnp | p _ n hn hp]; last 1 first.
- by have := (le_trans hn hp).
- have -> : p = 0 by apply/eqP; rewrite eq_le h0p hp0.
  by rewrite add0r.
case: (altP (n =P 0)) => [-> | hn0].
  by rewrite add0r.
case: (altP (n =P 1)) => [-> | hn1].
  by rewrite addrC.
case: (altP (n =P 2)) => [-> | hn2].
  by rewrite addrC.
case: (altP (n =P 3)) => [-> | hn3].
  by rewrite addrC.
clear ebk0 ebk1 ebk2 ebk3.
(* Again a variable change. *)
pose m : int := n - (4 : int); simpl in m.
have hm : n = m + 4 by rewrite /m addrK.
have le0m : m >= 0.
  by move: le0n hn0 hn1 hn2 hn3; rewrite hm; clear; goal_to_lia; intlia.
have hmp : m + 3 <= p.
  move: hnp; rewrite -addn1 PoszD hm; clear; goal_to_lia; intlia.
rewrite hm; clearbody m; clear le0n hnp hn0 hn1 hn2 hn3 hm n.
have -> : m + 4 + k = int.shift 4 (m + k).
  by rewrite int.shift2Z addrAC.
have b'_Sn4_from2 (n : int) : (2 : int) <= n -> 
                               annotated_recs_v.P_horner b' n = 0.
  by move=> hn; apply: b'_Sn4; apply: le_trans hn.
have hmk2 : (2 : int) <= m + k by move: kpos le0m; clear; intlia.
rewrite (Sn4_flat_to_Sn4_rew b'_Sn4_from2 hmk2); clear b'_Sn4_from2.
rewrite (Sn4_flat_to_Sn4_rew algo_closures.b_Sn4 hmk2); clear hmk2.
rewrite !int.shift2Z ![m + k + _]addrAC.
by do 4! (rewrite ihp; [ | (goal_to_lia; intlia) ..]).
Qed.

(* Maybe should part of this go to initial_conds. *)
Lemma b'_eq_b (n : int) : n >= Posz 2 -> b' n = b n.
Proof.
apply: b'_eq_b_reduction => //.
- by rewrite b'2_eq initial_conds.b2_eq.
- by rewrite b'3_eq initial_conds.b3_eq.
- rewrite -[(2 : int) + (2 : int)]/(int.shift 2 2).
  rewrite b'_Sn2_rew // b'2_eq b'3_eq.
  rewrite /annotated_recs_c.P_cf0 /annotated_recs_c.P_cf1.
  rewrite /annotated_recs_c.P_cf2.
  initial_conds.expand_b.
  rat_field.
  do 9! (split; first by move/eqP; rewrite rat_of_Z_eq0).
  by move/eqP; rewrite rat_of_Z_eq0.
- rewrite -[(2 : int) + (3 : int)]/(int.shift 2 3).
  rewrite b'_Sn2_rew // b'3_eq b'4_eq.
  rewrite /annotated_recs_c.P_cf0 /annotated_recs_c.P_cf1.
  rewrite /annotated_recs_c.P_cf2.
  initial_conds.expand_b.
  rat_field.
  initial_conds.try_solve_numeral_intia_obligations.
  by rewrite rat_of_Z_eq0.
Qed.

Lemma b_Sn2_almost (n : int) : n >= (2 : int) ->
                                annotated_recs_c.P_horner b n = 0.
Proof.
move=> h.
rewrite /annotated_recs_c.P_horner/punk.horner_seqop [LHS]/=.
rewrite -!b'_eq_b; [ | (goal_to_lia; intlia) ..].
have h' : 0 <= n by intlia.
rewrite b'_Sn2_rew //.
rat_field.
rewrite /annotated_recs_c.P_cf2.
apply/eqP.
apply: expfz_neq0.
by apply: lt0r_neq0; affine_poly_intlia.
Qed.

Lemma b_Sn2_at_0 : annotated_recs_c.P_horner b 0 = 0.
Proof.
rewrite  /annotated_recs_c.P_horner /punk.horner_seqop /=.
rewrite initial_conds.b0_eq initial_conds.b1_eq initial_conds.b2_eq.
rewrite /annotated_recs_c.P_cf1 /annotated_recs_c.P_cf2.
rat_field.
goal_to_lia.
intlia.
Qed.

Lemma b_Sn2_at_1 : annotated_recs_c.P_horner b 1 = 0.
Proof.
rewrite /annotated_recs_c.P_horner /punk.horner_seqop /=.
rewrite initial_conds.b1_eq initial_conds.b2_eq initial_conds.b3_eq.
rewrite /annotated_recs_c.P_cf0 /annotated_recs_c.P_cf1 /annotated_recs_c.P_cf2.
rat_field.
goal_to_lia.
intlia.
Qed.

Lemma b_Sn2 (n : int) : n >= 0 -> annotated_recs_c.P_horner b n = 0.
Proof.
move=> hn.
case: (altP (n =P 0)) => [-> | h0]; first exact: b_Sn2_at_0.
case: (altP (n =P 1)) => [-> | h1]; first exact: b_Sn2_at_1.
pose p : int := n - (2 : int); simpl in p.
have hnp : n = p + (2 : int) by rewrite /p addrNK.
have {hn h0 h1} le0p : 0 <= p.
  by move: hn h0 h1; rewrite hnp; clear; goal_to_lia; intlia.
have {le0p hnp p} h : (2 : int) <= n.
  by rewrite hnp ler_addr.
exact: b_Sn2_almost.
Qed.

End ReduceBToOrder2.
