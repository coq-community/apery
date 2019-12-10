Load "include/ops_header.v".

Definition precond_Sn (n k : int) :=
  (n >= 0) /\ (k >= 0) /\ (n + 1 != 0) /\ (k != n + 1).
  
Definition precond_Sk (n k : int) :=
  (n >= 0) /\ (k >= 0) /\
  (n != 3%:R * k + 1) /\ (n != 3%:R * k + 2) /\
  (n != 3%:R * k + 3).

Load "include/ann_nm_u.v".


Record Ann u : Type := ann {
  Sn_ : Sn u;
  Sk_ : Sk u
}.


Section CTOfu.

Variable u : int -> int -> rat.
Variable ann : Ann u.
Let u_Sn := Sn_ ann.
Let u_Sk := Sk_ ann.

Definition not_D (n k : int) :=
  (0 <= n) && (0 <= k) && (n != 3%:R * k + 1) && (n != 3%:R * k + 2) &&
  (n != 3%:R * k + 3) && (k != n) && (k != n + 1) && (k != n + 2).

Theorem P_eq_Delta_Q (n k : int) :
  not_D n k -> P_horner (u ^~ k) n = Q_flat u n (int.shift 1 k) - Q_flat u n k.
Proof.
rewrite /not_D; andb_to_and => notD.
rewrite /P_horner /P_seq /punk.horner_seqop /= /Q_flat.
do 2! (rewrite u_Sn; last by rewrite /precond_Sn; intlia).
rewrite u_Sk; last by rewrite /precond_Sk; intlia.
rewrite /P_cf0 /P_cf1 /P_cf2 /Q_cf0_0 /Sn_cf0_0 /Sk_cf0_0.
rewrite !int.shift2R.
rat_field.
by goal_to_lia; intlia.
Qed.

End CTOfu.
