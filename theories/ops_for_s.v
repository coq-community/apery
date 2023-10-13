Load "include/ops_header.v".

Require annotated_recs_d.


(* Shorter name space for elements in annotated_recs_d *)
Module d.
Include annotated_recs_d.
End d.

Require Import annotated_recs_s.

Section AnnOfS.

Variable d : int -> int -> int -> rat.
Variable d_ann : d.Ann d.
Let d_Sn := d.Sn_ d_ann.
Let d_Sk := d.Sk_ d_ann.
Let d_Sm := d.Sm_ d_ann.

Theorem P1_eq_Delta_Q1 : d.CT1 d.
Proof.
move=> n m k; rewrite /d.not_D1 => ?.
rewrite /d.P1_horner /d.P1_seq.
rewrite /punk.biv_horner_seqop2 /punk.biv_horner_seqop.
rewrite /punk.biv_horner_seqop_rec /punk.pfun2 /d.Q1_flat /=.
do 4! (rewrite d_Sn; last by rewrite /d.precond.Sn; lia).
do 2! rewrite d_Sk //.
rewrite d_Sm; last by rewrite /d.precond.Sm; lia.
set d_nmk := d _ _ _.
Fail set dtest := d _ _ _.
rewrite
  /d.P1_cf0_0 /d.P1_cf0_1 /d.P1_cf1_0 /d.P1_cf1_1 /d.P1_cf2_0
  /d.Q1_cf0_0_0 /d.Q1_cf0_1_0 /d.Q1_cf1_0_0
  /d.Sk_cf0_0_0 /d.Sm_cf0_0_0 /d.Sn_cf0_0_0.
rewrite !int.shift2R.
by field; ring_lia.
Qed.

Theorem P2_eq_Delta_Q2 : d.CT2 d.
Proof.
move=> n m k; rewrite /d.not_D2 => ?.
rewrite /d.P2_horner /d.P2_seq.
rewrite /punk.biv_horner_seqop2 /punk.biv_horner_seqop.
rewrite /punk.biv_horner_seqop_rec /punk.pfun2 /d.Q2_flat /=.
do 6! (rewrite d_Sn; last by rewrite /d.precond.Sn; lia).
rewrite d_Sm; last by rewrite /d.precond.Sm; lia.
set d_nmk := d _ _ _.
Fail set dtest := d _ _ _.
rewrite
  /d.P2_cf0_0 /d.P2_cf1_0 /d.P2_cf2_0 /d.P2_cf3_0
  /d.Q2_cf0_0_0 /d.Q2_cf1_0_0 /d.Q2_cf2_0_0
  /d.Sk_cf0_0_0 /d.Sm_cf0_0_0 /d.Sn_cf0_0_0.
rewrite !int.shift2R.
by field; ring_lia.
Qed.

Theorem P3_eq_Delta_Q3 : d.CT3 d.
Proof.
move => n m k; rewrite /d.not_D3 => ?.
rewrite /d.P3_horner /d.P3_seq /punk.biv_horner_seqop2 /punk.biv_horner_seqop.
rewrite /punk.biv_horner_seqop_rec /punk.pfun2 /d.Q3_flat /=.
do 2! (rewrite d_Sn; last by rewrite /d.precond.Sn; lia).
rewrite d_Sk //.
rewrite d_Sm; last by rewrite /d.precond.Sm; lia.
set d_nmk := d _ _ _.
Fail set dtest := d _ _ _.
rewrite
  /d.P3_cf0_0 /d.P3_cf0_1 /d.P3_cf1_0 /d.P3_cf1_1 /d.Q3_cf0_0_0
  /d.Sk_cf0_0_0 /d.Sm_cf0_0_0 /d.Sn_cf0_0_0.
by field; ring_lia.
Qed.

Theorem P4_eq_Delta_Q4 : d.CT4 d.
Proof.
move => n m k; rewrite /d.not_D4 => ?.
rewrite /d.P4_horner /d.P4_seq /punk.biv_horner_seqop2 /punk.biv_horner_seqop.
rewrite /punk.biv_horner_seqop_rec /punk.pfun2 /d.Q4_flat /=.
do 2! rewrite d_Sk //.
rewrite d_Sm; last by rewrite /d.precond.Sm; lia.
set d_nmk := d _ _ _.
Fail set dtest := d _ _ _.
rewrite
  /d.P4_cf0_0 /d.P4_cf0_1 /d.P4_cf0_2 /d.Q4_cf0_0_0
  /d.Sk_cf0_0_0 /d.Sm_cf0_0_0 /d.Sn_cf0_0_0.
by field; ring_lia.
Qed.


Definition P1_horner := d.P1_horner.
Definition P2_horner := d.P2_horner.
Definition P3_horner := d.P3_horner.
Definition P4_horner := d.P4_horner.
Definition P1_flat := d.P1_flat.
Definition P2_flat := d.P2_flat.
Definition P3_flat := d.P3_flat.
Definition P4_flat := d.P4_flat.


Let s (n k : int) : rat := \sum_(1 <= m < k + 1 :> int) d n k m.


Ltac rewrite_modulo_d_ann expr :=
  do ? (rewrite d_Sm in expr *; rewrite /d.precond.Sm; [ | lia]);
  do ? (rewrite d_Sk in expr *; rewrite /d.precond.Sk; [ | done]);
  do ? (rewrite d_Sn in expr *; rewrite /d.precond.Sn; [ | lia]).


Theorem recD1 (n k : int) : 0 <= k -> k < n -> P1_horner s n k = 0.
Proof.
move=> ? ?.
rewrite /P1_horner /d.P1_horner.
rewrite (punk.biv_sound_telescoping P1_eq_Delta_Q1); last by rewrite lerDr.
set telQ := (X in X + _ + _).
set onD := (X in _ + X + _).
set remP := (X in _ + _ + X).

rewrite [bigop]unlock /= !add0r !addr0 in remP *.

rewrite_modulo_d_ann remP.

rewrite {}/telQ /d.Q1_flat.
set telQ := (X in X + _ + _).

rewrite_modulo_d_ann telQ.

have -> : onD = 0.
  rewrite /onD {remP telQ}.

  set F := BIG_F.
  clearbody F.

  rewrite big_int_cond /=.
  apply: big_pred0 => i.

  rewrite /d.not_D1.
  lia.

rewrite {}/telQ {}/remP.
rewrite !int.shift2Z !addr0.
set d1 := d _ _ _.
set d2 := d _ _ _.
rewrite
  /d.P1_cf0_1 /d.P1_cf1_1
  /d.Q1_cf0_0_0 /d.Q1_cf0_1_0 /d.Q1_cf1_0_0
  /d.Sn_cf0_0_0 /d.Sk_cf0_0_0 /d.Sm_cf0_0_0.
by field; ring_lia.
Qed.


Theorem recD2 (n k : int) : 0 < k -> k < n -> P2_horner s n k = 0.
Proof.
move=> ? ?.
rewrite /P2_horner /d.P2_horner.
rewrite (punk.biv_sound_telescoping P2_eq_Delta_Q2); last by rewrite ler_wpDr.
set telQ := (X in X + _ + _).
set onD := (X in _ + X + _).
set remP := (X in _ + _ + X).

rewrite [bigop]unlock /= !add0r in remP *.
rewrite {}/remP.

rewrite {}/telQ /d.Q2_flat.
set telQ := (X in X + _ + _).

rewrite_modulo_d_ann telQ.

have -> : onD = 0.
  rewrite /onD {telQ}.

  set F := BIG_F.
  clearbody F.

  rewrite big_int_cond /=.
  apply: big_pred0 => i.

  rewrite /d.not_D2.
  lia.

rewrite {}/telQ.
rewrite !int.shift2Z !addr0.
set d1 := d _ _ _.
set d2 := d _ _ _.
rewrite
  /d.Q2_cf0_0_0 /d.Q2_cf1_0_0 /d.Q2_cf2_0_0
  /d.Sn_cf0_0_0 /d.Sk_cf0_0_0 /d.Sm_cf0_0_0.
by field; ring_lia.
Qed.


Theorem recD3 (n k : int) : 0 <= k -> k < n -> P3_horner s n k = 0.
Proof.
move=> ? ?.
rewrite /P3_horner /d.P3_horner.
rewrite (punk.biv_sound_telescoping P3_eq_Delta_Q3); last by rewrite lerDr.
set telQ := (X in X + _ + _).
set onD := (X in _ + X + _).
set remP := (X in _ + _ + X).

rewrite [bigop]unlock /= !add0r !addr0 in remP *.

rewrite_modulo_d_ann remP.

rewrite {}/telQ /d.Q3_flat.
set telQ := (X in X + _ + _).

rewrite_modulo_d_ann telQ.

have -> : onD = 0.
  rewrite /onD {remP telQ}.

  set F := BIG_F.
  clearbody F.

  rewrite big_int_cond /=.
  apply: big_pred0 => i.

  rewrite /d.not_D3.
  lia.

rewrite {}/telQ {}/remP.
rewrite !addr0.
set d1 := d _ _ _.
set d2 := d _ _ _.
rewrite
  /d.P3_cf0_1 /d.P3_cf1_1 /d.Q3_cf0_0_0
  /d.Sn_cf0_0_0 /d.Sk_cf0_0_0 /d.Sm_cf0_0_0.
rewrite !int.shift2R.
by field; ring_lia.
Qed.


Theorem recD4 (n k : int) : 0 <= k -> k + 1 < n -> P4_horner s n k = 0.
Proof.
move=> ? ?.
rewrite /P4_horner /d.P4_horner.
rewrite (punk.biv_sound_telescoping P4_eq_Delta_Q4); last by rewrite lerDr.
set telQ := (X in X + _ + _).
set onD := (X in _ + X + _).
set remP := (X in _ + _ + X).

rewrite [bigop]unlock /= !add0r !addr0 in remP *.


do 1! (rewrite d_Sm in remP *; rewrite /d.precond.Sm; [ | lia]).
do ! (rewrite d_Sk in remP *; rewrite /d.precond.Sk; [ | done]).

rewrite {}/telQ /d.Q4_flat.
set telQ := (X in X + _ + _).

rewrite_modulo_d_ann telQ.

have -> : onD = 0.
  rewrite /onD {remP telQ}.

  set F := BIG_F.
  clearbody F.

  rewrite big_int_cond /=.
  apply: big_pred0 => i.

  rewrite /d.not_D4.
  lia.

rewrite {}/telQ {}/remP.
rewrite !addr0.
set d1 := d _ _ _.
set d2 := d _ _ _.
rewrite
  /d.P4_cf0_1 /d.P4_cf0_2 /d.Q4_cf0_0_0
  /d.Sn_cf0_0_0 /d.Sk_cf0_0_0 /d.Sm_cf0_0_0.
rewrite !int.shift2R.
by field; ring_lia.
Qed.


(* Flat variants of the four lemmas above. *)

Lemma recD1_flat (n k : int) : P1_flat s n k = P1_horner s n k.
Proof.
rewrite /P1_flat /d.P1_flat /P1_horner /d.P1_horner.
rewrite /punk.biv_horner_seqop2 /punk.biv_horner_seqop.
rewrite /punk.biv_horner_seqop_rec /=.
set s1 := s _ _.
set s2 := s _ _.
set s3 := s _ _.
set s4 := s _ _.
set s5 := s _ _.
ring.
Qed.

Lemma recD2_flat (n k : int) : P2_flat s n k = P2_horner s n k.
Proof.
rewrite /P2_flat /d.P2_flat /P2_horner /d.P2_horner.
rewrite /punk.biv_horner_seqop2 /punk.biv_horner_seqop.
rewrite /punk.biv_horner_seqop_rec /=.
set s1 := s _ _.
set s2 := s _ _.
set s3 := s _ _.
set s4 := s _ _.
ring.
Qed.

Lemma recD3_flat (n k : int) : P3_flat s n k = P3_horner s n k.
Proof.
rewrite /P3_flat /d.P3_flat /P3_horner /d.P3_horner.
rewrite /punk.biv_horner_seqop2 /punk.biv_horner_seqop.
rewrite /punk.biv_horner_seqop_rec /=.
set s1 := s _ _.
set s2 := s _ _.
set s3 := s _ _.
set s4 := s _ _.
ring.
Qed.

Lemma recD4_flat (n k : int) : P4_flat s n k = P4_horner s n k.
Proof.
rewrite /P4_flat /d.P4_flat /P4_horner /d.P4_horner.
rewrite /punk.biv_horner_seqop2 /punk.biv_horner_seqop.
rewrite /punk.biv_horner_seqop_rec /=.
set s1 := s _ _.
set s2 := s _ _.
set s3 := s _ _.
ring.
Qed.


Lemma s_Sn2 : Sn2 s.
Proof.
rewrite /Sn2 /precond.Sn2 => n k [ltk0 ltkn].
have Sn2_lcomb_eq_0 : Sn2_lcomb s n k = 0.
  rewrite /Sn2_lcomb /Sn2_lcomb_cf2 /Sn2_lcomb_cf4.
  by rewrite -/P1_flat recD1_flat recD1 // -/P3_flat recD3_flat recD3 //; ring.
apply/eqP.
rewrite -subr_eq0.
set nzero := Sn2_lcomb_cf1 n k * d.P1_cf2_0 n k.
have nzero_n0 : nzero != 0.
  by rewrite mulf_eq0 expfz_eq0 /Sn2_lcomb_cf1; ring_lia.
rewrite -(mulrI_eq0 _ (lregP nzero_n0)) {nzero_n0}.
rewrite -Sn2_lcomb_eq_0.
apply/eqP.
rewrite /Sn2_cf0_0 /Sn2_cf1_0 /Sn2_cf0_1 /nzero /Sn2_lcomb.
rewrite /Sn2_lcomb_cf1 /Sn2_lcomb_cf2 /Sn2_lcomb_cf3 /Sn2_lcomb_cf4.
rewrite
  /d.P1_flat /d.P2_flat /d.P3_flat /d.P4_flat.
rewrite
  /d.P1_cf0_0 /d.P1_cf0_1 /d.P1_cf1_0
  /d.P1_cf1_1 /d.P1_cf2_0
  /d.P2_cf0_0 /d.P2_cf1_0 /d.P2_cf2_0
  /d.P2_cf3_0
  /d.P3_cf0_0 /d.P3_cf0_1 /d.P3_cf1_0
  /d.P3_cf1_1 /d.P4_cf0_0 /d.P4_cf0_1
  /d.P4_cf0_2.
by field; ring_lia.
Qed.

Lemma s_SnSk : SnSk s.
Proof.
  rewrite /SnSk /precond.SnSk => n k [ltk0 ltkn].
have SnSk_lcomb_eq_0 : SnSk_lcomb s n k = 0.
  rewrite /SnSk_lcomb /SnSk_lcomb_cf1 /SnSk_lcomb_cf2 /SnSk_lcomb_cf3.
  by rewrite /SnSk_lcomb_cf4 -/P3_flat recD3_flat recD3 //; ring.
apply/eqP.
rewrite -subr_eq0.
set nzero := d.P3_cf1_1 n k.
have nzero_n0 : nzero != 0 by rewrite /nzero /d.P3_cf1_1; ring_lia.
rewrite -(mulrI_eq0 _ (lregP nzero_n0)) // {nzero_n0}.
rewrite -SnSk_lcomb_eq_0.
apply/eqP.
rewrite /SnSk_cf0_0 /SnSk_cf1_0 /SnSk_cf0_1 /nzero /SnSk_lcomb.
rewrite /SnSk_lcomb_cf1 /SnSk_lcomb_cf2 /SnSk_lcomb_cf3 /SnSk_lcomb_cf4.
rewrite
  /d.P1_flat /d.P2_flat /d.P3_flat /d.P4_flat.
rewrite
  /d.P1_cf0_0 /d.P1_cf0_1 /d.P1_cf1_0
  /d.P1_cf1_1 /d.P1_cf2_0
  /d.P2_cf0_0 /d.P2_cf1_0 /d.P2_cf2_0
  /d.P2_cf3_0
  /d.P3_cf0_0 /d.P3_cf0_1 /d.P3_cf1_0
  /d.P3_cf1_1 /d.P4_cf0_0 /d.P4_cf0_1
  /d.P4_cf0_2.
by field; ring_lia.
Qed.

Lemma s_Sk2 : Sk2 s.
Proof.
  rewrite /Sk2 /precond.Sk2 => n k [ltk0 ltSkn].
have Sk2_lcomb_eq_0 : Sk2_lcomb s n k = 0.
  rewrite /Sk2_lcomb /Sk2_lcomb_cf1 /Sk2_lcomb_cf2 /Sk2_lcomb_cf3.
  by rewrite /Sk2_lcomb_cf4 -/P4_flat recD4_flat recD4 //; ring.
apply/eqP.
rewrite -subr_eq0.
set nzero := d.P4_cf0_2 n k.
have nzero_n0 : nzero != 0 by rewrite /nzero /d.P4_cf0_2 !mulf_eq0; ring_lia.
rewrite -(mulrI_eq0 _ (lregP nzero_n0)) // {nzero_n0}.
rewrite -Sk2_lcomb_eq_0.
apply/eqP.
rewrite /Sk2_cf0_0 /Sk2_cf0_1 /nzero /Sk2_lcomb.
rewrite /Sk2_lcomb_cf1 /Sk2_lcomb_cf2 /Sk2_lcomb_cf3 /Sk2_lcomb_cf4.
rewrite
  /d.P1_flat /d.P2_flat /d.P3_flat /d.P4_flat.
rewrite
  /d.P1_cf0_0 /d.P1_cf0_1 /d.P1_cf1_0
  /d.P1_cf1_1 /d.P1_cf2_0
  /d.P2_cf0_0 /d.P2_cf1_0 /d.P2_cf2_0
  /d.P2_cf3_0
  /d.P3_cf0_0 /d.P3_cf0_1 /d.P3_cf1_0
  /d.P3_cf1_1 /d.P4_cf0_0 /d.P4_cf0_1
  /d.P4_cf0_2.
by field; ring_lia.
Qed.

End AnnOfS.
