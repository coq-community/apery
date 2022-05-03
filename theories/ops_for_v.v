Load "include/ops_header.v".

Require annotated_recs_c annotated_recs_s.
Require Import annotated_recs_v.

(* Shorter name space for elements in annotated_recs_[c|u|v] *)
Module c.
Include annotated_recs_c.
End c.

(* Remember that u shares the same annihilators as s. *)
Module u.
Include annotated_recs_s.
End u.

Module v.
Include annotated_recs_v.
End v.

Section AnnOfV.

Variable c : int -> int -> rat.
Variable u : int -> int -> rat.

Variable c_ann : c.Ann c.
Let c_Sn := c.Sn_ c_ann.
Let c_Sk := c.Sk_ c_ann.


Variable u_ann : u.Ann u.

Let u_Sn2 := u.Sn2_ u_ann.
Let u_SnSk := u.SnSk_ u_ann.
Let u_Sk2 := u.Sk2_ u_ann.

Let v n k := c n k * u n k.

Lemma v_Sk2 : Sk2 v.
Proof.
rewrite /Sk2 /precond.Sk2.
move=> n k ?.
rewrite /v.
do 1! (rewrite u_Sk2; last by rewrite /annotated_recs_s.precond.Sk2; lia).
set u1 := u _ _.
set u2 := u _ _.
do 3! (rewrite c_Sk; last by rewrite /c.precond.Sk; lia).
set c1 := c _ _.
rewrite
  /c.Sk_cf0_0 /annotated_recs_s.Sk2_cf0_0 /annotated_recs_s.Sk2_cf0_1
  /Sk2_cf0_0 /Sk2_cf0_1 !int.shift2R.
by field; ring_lia.
Qed.

Lemma v_SnSk : SnSk v.
Proof.
rewrite /SnSk /precond.SnSk.
move=> n k ?.
rewrite /v.
do 1! (rewrite u_SnSk; last by rewrite /annotated_recs_s.precond.SnSk; lia).
set u1 := u _ _.
set u2 := u _ _.
set u3 := u _ _. (* set u4 := u _ _.*)
do 2! (rewrite c_Sn; last by rewrite /c.precond.Sn; lia).
do 1! (rewrite c_Sk; last by rewrite /c.precond.Sk; lia).
set c1 := c _ _.
(* set c2 := c _ _. *)
rewrite /c.Sn_cf0_0 /c.Sk_cf0_0 !int.shift2R.
rewrite /annotated_recs_s.SnSk_cf0_0 /annotated_recs_s.SnSk_cf1_0.
rewrite  /annotated_recs_s.SnSk_cf0_1 /SnSk_cf0_0 /SnSk_cf1_0 /SnSk_cf0_1.
by field; ring_lia.
Qed.

Lemma v_Sn2 : Sn2 v.
Proof.
rewrite /Sn2 /precond.Sn2.
move=> n k ?.
rewrite /v.
do 1! (rewrite u_Sn2; last by rewrite /annotated_recs_s.precond.Sn2; lia).
set u1 := u _ _.
set u2 := u _ _.
set u3 := u _ _.
do 3! (rewrite c_Sn; last by rewrite /c.precond.Sn; lia).
do 1! (rewrite c_Sk; last by rewrite /c.precond.Sk; lia).
set c1 := c _ _.
(* set c2 := c _ _.*)
rewrite /c.Sn_cf0_0 /c.Sk_cf0_0 !int.shift2R.
rewrite /Sn2_cf0_0 /Sn2_cf1_0 /Sn2_cf0_1.
rewrite /annotated_recs_s.Sn2_cf0_0 /annotated_recs_s.Sn2_cf1_0.
rewrite /annotated_recs_s.Sn2_cf0_1.
by field; ring_lia.
Qed.

End AnnOfV.
