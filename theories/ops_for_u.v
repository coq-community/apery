Load "include/ops_header.v".

Require annotated_recs_z annotated_recs_s.

(* Shorter name space for elements in annotated_recs_[z|s] *)
Module z.
Include annotated_recs_z.
End z.

Module s.
Include annotated_recs_s.
End s.



Section AnnOfU.

Variable z : int -> rat.
Variable s : int -> int -> rat.

Variable z_ann : z.Ann z.
Let z_Sn2 := z.Sn2_ z_ann.

Variable s_ann : s.Ann s.
Let s_Sn2 := s.Sn2_ s_ann.
Let s_SnSk := s.SnSk_ s_ann.
Let s_Sk2 := s.Sk2_ s_ann.


Let u n k := z n + s n k.

Lemma u_Sk2 : s.Sk2 u.
Proof.
(* Hack to force the lemma to depend on unused parameter. *)
have ? := z_ann.
rewrite /s.Sk2 /s.precond.Sk2.
move => n k ?.
rewrite /u.
rewrite s_Sk2 //.
set s1 := s _ _.
set s2 := s _ _.
set z1 := z _.
rewrite /s.Sk2_cf0_0 /s.Sk2_cf0_1.
rat_field.
rewrite /emb /emb0; goal_to_lia; intlia.
Qed.

Lemma u_SnSk : s.SnSk u.
Proof.
(* Hack to force the lemma to depend on unused parameter. *)
have ? := z_ann.
rewrite /s.SnSk /s.precond.SnSk.
move => n k ?.
rewrite /u.
rewrite s_SnSk //.
set s1 := s _ _.
set s2 := s _ _.
set s3 := s _ _.
set z1 := z _.
set z2 := z _.
rewrite /s.SnSk_cf0_0 /s.SnSk_cf1_0 /s.SnSk_cf0_1.
rat_field.
rewrite /emb /emb0; goal_to_lia; intlia.
Qed.

Lemma u_Sn2 : s.Sn2 u.
Proof.
rewrite /s.Sn2 /s.precond.Sn2.
move => n k ?.
rewrite /u.
rewrite z_Sn2; last by rewrite /z.precond.Sn2; intlia.
rewrite s_Sn2 //.
set s1 := s _ _.
set s2 := s _ _.
set s3 := s _ _.
set z1 := z _.
set z2 := z _.
rewrite /z.Sn2_cf0 /z.Sn2_cf1
  /s.Sn2_cf0_0 /s.Sn2_cf1_0 /s.Sn2_cf0_1.
rat_field.
rewrite /emb /emb0; goal_to_lia; intlia.
Qed.

End AnnOfU.
