Load "include/ops_header.v".

Require annotated_recs_c.

Module c.
Include annotated_recs_c.
End c.


Section AnnOfA.

Variable c : int -> int -> rat.
Variable c_ann : c.Ann c.
Let c_Sn := c.Sn_ c_ann.
Let c_Sk := c.Sk_ c_ann.

Theorem P_eq_Delta_Q : c.CT c.
Proof.
move=> n k; rewrite /c.CT /c.not_D => notD.
rewrite /c.P_horner /c.P_seq /punk.horner_seqop /= /c.Q_flat.
do 2! (rewrite c_Sn ; last by rewrite /c.precond.Sn; lia).
rewrite c_Sk; last by rewrite /c.precond.Sk; lia.
rewrite /c.P_cf0 /c.P_cf1 /c.P_cf2 /c.Q_cf0_0 /c.Sn_cf0_0 /c.Sk_cf0_0.
(* The following rewriting is unavoidable since fractions in the shift lemmas
   for c involve (k + ...)%:~R as soon as we shift more than one time. *)
rewrite !int.shift2R.
by field; ring_lia.
Qed.

Let a (n : int) : rat := \sum_(0 <= k < n + 1 :> int) (c n k).

Theorem recAperyA (n : int) : 2 <= n :> int -> c.P_horner a n = 0.
Proof.
move=> nge2.
rewrite /c.P_horner (punk.sound_telescoping P_eq_Delta_Q); last lia.
set telQ := (X in X + _ + _).
set onD := (X in _ + X + _).
set remP := (X in _ + _ + X).
(* Now this part is possibly different for each application of CT. *)
have onDE : onD =
    c.P_horner (c ^~ n) n - (c.Q_flat c n (int.shift 1 n) - c.Q_flat c n n).
  rewrite /onD /c.not_D big_int_cond (eq_bigl (pred1 n)) => [|? /=]; last lia.
  by rewrite big_pred1_eqz ifT //; lia.
(* We simplify using the cancellations of onD with telQ. *)
(* This step is REQUIRED because terms in onD have potential divisions by 0. *)
have {telQ} -> : telQ + onD = c.P_horner (c ^~ n) n + c.Q_flat c n n.
  by rewrite onDE /telQ /c.Q_flat /c.Q_cf0_0 /int.shift /= /int.shift1; ring.
(* Unrolling the sum of shifts: this depend only on the order of P. *)
rewrite {}/remP [bigop]unlock /= !add0r !addr0 -!int.shift2Z.
(* Strategy to normalize the expression without using forbidden paths. *)
rewrite /c.P_horner /c.P_seq /punk.horner_seqop /=.
rewrite /c.Q_flat.
(* Ensure shifts are in normal form. *)
have -> : int.shift1 n = int.shift 1 n by done.
rewrite int.shift0 int.shiftS.
(* Perform the reduction in the order of a Gröbner-based reduction. *)
rewrite (@c_Sk (int.shift 2 n) (int.shift 1 n)); last first.
  by rewrite /c.precond.Sk; lia.
rewrite (@c_Sk (int.shift 2 n) n); last by rewrite /c.precond.Sk; lia.
rewrite (@c_Sk (int.shift 1 n) n); last by rewrite /c.precond.Sk; lia.
rewrite (@c_Sn (int.shift 1 n) n); last by rewrite /c.precond.Sn; lia.
rewrite (@c_Sn n n); last by rewrite /c.precond.Sn; lia.
set c1 := c _ _.
Fail set c2 := c _ _.
rewrite
  /c.Sn_cf0_0 /c.Sk_cf0_0
  /c.P_cf0 /c.P_cf1 /c.P_cf2
  /c.Q_flat /c.Q_cf0_0
  !int.shift2R.
by field; ring_lia.
Qed.

End AnnOfA.
