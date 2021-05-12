(* In this file, we now propagate the theories in the ops_for_x files to
   prove results on our concrete sequences defined in seq_defs.v. *)

Require Import Psatz ZArith.

From mathcomp Require Import all_ssreflect all_algebra.
Require Import binomialz bigopz.
Require Import field_tactics lia_tactics shift.
Require Import seq_defs.

Require harmonic_numbers.
Require ops_for_a ops_for_b  ops_for_s ops_for_u ops_for_v.

Require annotated_recs_c.
Require annotated_recs_z.
Require annotated_recs_d.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Import GRing.Theory.

(* First, a few lemmas to avoid repeated 'have ...' in the proofs. *)

Lemma middle_1 (a b : int) : a + 1 + b = a + b + 1.
Proof.  by rewrite addrAC. Qed.

Lemma alt_sign (a : int) : (-1) ^ (a + 1) = - (-1) ^ a :> rat.
Proof.  by rewrite exprzDr // expr1z mulrN1.  Qed.

(* Then, the propagation of the theories.*)

Lemma c_Sn : annotated_recs_c.Sn c.
Proof.
rewrite /annotated_recs_c.Sn /annotated_recs_c.precond.Sn => n k ?.
rewrite /c.
rewrite middle_1 !binSz; [| intlia..].
rewrite rmorphD /=.
set b1 := binomialz _ _.
set b2 := binomialz _ _.
rewrite /annotated_recs_c.Sn_cf0_0.
rat_field.
by goal_to_lia; intlia.
Qed.


Lemma c_Sk : annotated_recs_c.Sk c.
Proof.
rewrite /annotated_recs_c.Sk /annotated_recs_c.precond.Sk => n k ?.
rewrite /c.
rewrite addrA.
rewrite !(binSz, binzS) //; [ | intlia ..].
rewrite !rmorphD /=.
set b1 := binomialz _ _.
set b2 := binomialz _ _.
rewrite /annotated_recs_c.Sk_cf0_0.
rat_field.
by goal_to_lia; intlia.
Qed.

Definition c_ann := annotated_recs_c.ann c_Sn c_Sk.

Lemma a_Sn2 (n : int) : (2 : int) <= n -> annotated_recs_c.P_horner a n = 0.
Proof.
move=> h.
apply: (ops_for_a.recAperyA c_ann h).
Qed.

Lemma d_Sn : annotated_recs_d.Sn d.

Proof.
rewrite /annotated_recs_d.Sn /annotated_recs_d.precond.Sn => n k m ?.
rewrite /d.
rewrite middle_1 !binSz; [ | by intlia ..].
set b1 := binomialz _ _.
set b2 := binomialz _ _.
rewrite rmorphD /= /annotated_recs_d.Sn_cf0_0_0.
rat_field.
have : exists e1 : int, b1 = e1%:~R /\ e1 > 0 by apply: bin_nonneg_int; intlia.
case=> e1.  case=> -> {b1} e1_pos.
have : exists e2 : int, b2 = e2%:~R /\ e2 > 0 by apply: bin_nonneg_int; intlia.
case=> e2.  case=> -> {b2} e2_pos.
by goal_to_lia; intlia.
Qed.

(* This is a fake recurrence, because d does not really depend on k *)
Lemma d_Sk : annotated_recs_d.Sk d.
Proof.
rewrite /annotated_recs_d.Sk /annotated_recs_d.precond.Sk => n k m ?.
by rewrite /annotated_recs_d.Sk_cf0_0_0 rat_of_ZEdef mul1r.
Qed.

Lemma d_Sm : annotated_recs_d.Sm d.
Proof.
rewrite /annotated_recs_d.Sm /annotated_recs_d.precond.Sm => n k m ?.
rewrite /d.
rewrite middle_1 !alt_sign rmorphD /=.
rewrite addrA.
rewrite !(binzS, binSz); [ | intlia ..].
set b1 := binomialz _ _.
set b2 := binomialz _ _.
rewrite /annotated_recs_d.Sm_cf0_0_0 !rmorphD /=.
rat_field.
have : exists e1 : int, b1 = e1%:~R /\ e1 > 0 by apply: bin_nonneg_int; intlia.
case=> e1.  case=> -> {b1} e1_pos.
have : exists e2 : int, b2 = e2%:~R /\ e2 > 0 by apply: bin_nonneg_int; intlia.
case=> e2.  case=> -> {b2} e2_pos.
by goal_to_lia; intlia.
Qed.

Definition d_ann := annotated_recs_d.ann d_Sn d_Sk d_Sm.

Lemma s_Sn2 : annotated_recs_s.Sn2 s.
Proof.
by apply: (ops_for_s.s_Sn2 d_ann).
Qed.

Lemma s_SnSk : annotated_recs_s.SnSk s.
Proof.
by apply: (ops_for_s.s_SnSk d_ann).
Qed.

Lemma s_Sk2 : annotated_recs_s.Sk2 s.
Proof.
by apply: (ops_for_s.s_Sk2 d_ann).
Qed.

Definition s_ann := annotated_recs_s.ann s_Sn2 s_SnSk s_Sk2.

Lemma z_Sn2 : annotated_recs_z.Sn2 ghn3.
Proof.
rewrite /annotated_recs_z.Sn2 /annotated_recs_z.precond.Sn2 => n ?.
rewrite /ghn3 harmonic_numbers.ghn_Sn2 -/ghn3; last by intlia.
set z1 := ghn3 _.
set z2 := ghn3 _.
rewrite /annotated_recs_z.Sn2_cf0 /annotated_recs_z.Sn2_cf1.
rat_field.
by goal_to_lia; intlia.
Qed.

Definition z_ann := annotated_recs_z.ann z_Sn2.

Lemma u_Sn2 : annotated_recs_s.Sn2 u.

Proof.
by apply: (ops_for_u.u_Sn2 z_ann s_ann).
Qed.

Lemma u_SnSk : annotated_recs_s.SnSk u.
Proof.
by apply: (ops_for_u.u_SnSk z_ann s_ann).
Qed.

Lemma u_Sk2 : annotated_recs_s.Sk2 u.
Proof.
by apply: (ops_for_u.u_Sk2 z_ann s_ann).
Qed.

Definition u_ann := annotated_recs_s.ann u_Sn2 u_SnSk u_Sk2.

Lemma v_Sn2 : annotated_recs_v.Sn2 v.
Proof.
by apply: (ops_for_v.v_Sn2 c_ann u_ann).
Qed.

Lemma v_SnSk : annotated_recs_v.SnSk v.
Proof.
by apply: (ops_for_v.v_SnSk c_ann u_ann).
Qed.

Lemma v_Sk2 : annotated_recs_v.Sk2 v.
Proof.
by apply: (ops_for_v.v_Sk2 c_ann u_ann).
Qed.

Definition v_ann := annotated_recs_v.ann v_Sn2 v_SnSk v_Sk2.

Lemma b_Sn4 (n : int) : n >= (2 : int) -> annotated_recs_v.P_horner b n = 0.
Proof.
move=> h.
by apply: (ops_for_b.recAperyB v_ann h).
Qed.
