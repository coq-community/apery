(* The goal of this file is to propose lemmas that decide the
   positivity (or non-nullity) of terms in rat, as well as to apply
   them to concrete values that will be used in the rest of the
   formalization. *)

Require Import Psatz ZArith.
From mathcomp Require Import all_ssreflect all_algebra.

Require Import field_tactics lia_tactics.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition is_fdiff_of (b a : int -> rat) :=
  forall n : int, n >= 0 -> a (n + 1) - a n = b n.

Lemma finite_diff_pos (a b : int -> rat) :
  is_fdiff_of b a -> a 0 > 0 ->
  (forall n : int, n >= 0 -> b n > 0) ->
  (forall n : int, n >= 0 -> a n > 0).
Proof.
move=> fdiff a0_pos cond_bn_pos n.
case: n => [o | //].
elim: o; first done.
move=> o.
set n := (Posz o).
have -> : Posz o.+1 = n + 1 by rewrite intS addrC.
have : n >= 0 by done.
move=> n_nonneg cond_an_pos _.
move: {cond_an_pos} (cond_an_pos n_nonneg) => an_pos.
move: {cond_bn_pos} (cond_bn_pos n n_nonneg) => bn_pos.
move: {fdiff} (fdiff n n_nonneg) => fdiff.
rewrite -{}fdiff in bn_pos.
have -> : a (n + 1) = a (n + 1) - a n + a n by rat_field.
apply: (ltr_spsaddl bn_pos an_pos).
Qed.

Definition p4 (n_ : int) : rat :=
  let n := n_%:~R : rat in
  rat_of_Z 12 * n^4 + rat_of_Z 96 * n^3 + rat_of_Z 283 * n^2 +
    rat_of_Z 364 * n + rat_of_Z 173.

Definition p3 (n_ : int) : rat :=
  let n := n_%:~R : rat in
  rat_of_Z 48 * n^3 + rat_of_Z 360 * n^2 + rat_of_Z 902 * n + rat_of_Z 755.

Definition p2 (n_ : int) : rat :=
  let n := n_%:~R : rat in
  rat_of_Z 144 * n^2 + rat_of_Z 864 * n + rat_of_Z 1310.

Definition p1 (n_ : int) : rat :=
  let n := n_%:~R : rat in
  rat_of_Z 288 * n + rat_of_Z 1008.

Definition p0 (n_ : int) : rat :=
  let n := n_%:~R : rat in
  rat_of_Z 288.

Lemma p3_is_fdiff_of_p4 : is_fdiff_of p3 p4.
Proof.
rewrite /is_fdiff_of => n pos_n.
rewrite /p3 /p4 rmorphD /=.
by rat_field.
Qed.

Lemma p2_is_fdiff_of_p3 : is_fdiff_of p2 p3.
Proof.
rewrite /is_fdiff_of => n pos_n.
rewrite /p2 /p3 rmorphD /=.
by rat_field.
Qed.

Lemma p1_is_fdiff_of_p2 : is_fdiff_of p1 p2.
Proof.
rewrite /is_fdiff_of => n pos_n.
rewrite /p1 /p2 rmorphD /=.
by rat_field.
Qed.

Lemma p0_is_fdiff_of_p1 : is_fdiff_of p0 p1.
Proof.
rewrite /is_fdiff_of => n pos_n.
rewrite /p0 /p1 rmorphD /=.
by rat_field.
Qed.

(* Take the evaluation at 0 of a polynomial in expanded form and normalize it
   to its constant term. *)
Ltac rat_simpl_poly_at_0 :=
  rewrite [rat_of_Z]lock ?{1}exp0rz /= ?{1}mulr0 ?{1}add0r; unlock.

Ltac pos_rat_of_Z := rewrite ltr0z /nat_of_P /Pmult_nat /=.

Lemma p4_0_pos : p4 0 > 0.
Proof.  
rewrite /p4.  rat_simpl_poly_at_0.  
rewrite rat_of_ZEdef.
by pos_rat_of_Z.  
Qed.

Lemma p3_0_pos : p3 0 > 0.
Proof.  
rewrite /p3.  rat_simpl_poly_at_0.  
rewrite rat_of_ZEdef.
by pos_rat_of_Z. 
 Qed.

Lemma p2_0_pos : p2 0 > 0.
Proof.  
rewrite /p2.  rat_simpl_poly_at_0.  
rewrite rat_of_ZEdef.
by pos_rat_of_Z.  
Qed.

Lemma p1_0_pos : p1 0 > 0.
Proof.  
rewrite /p1.  rat_simpl_poly_at_0.  
rewrite rat_of_ZEdef.
by pos_rat_of_Z.  
Qed.

Lemma p0_0_pos : p0 0 > 0.
Proof.  
rewrite /p0.
rewrite rat_of_ZEdef.
by pos_rat_of_Z.  
Qed.

Lemma p4_pos (n : int) : n >= 0 -> p4 n > 0.
Proof.
move=> h.
apply: (finite_diff_pos p3_is_fdiff_of_p4 p4_0_pos); last done.
move: n h => _ _ n h.
apply: (finite_diff_pos p2_is_fdiff_of_p3 p3_0_pos); last done.
move: n h => _ _ n h.
apply: (finite_diff_pos p1_is_fdiff_of_p2 p2_0_pos); last done.
move: n h => _ _ n h.
apply: (finite_diff_pos p0_is_fdiff_of_p1 p1_0_pos); last done.
move: n h => _ _ n h.
by rewrite /p0 rat_of_ZEdef ltr0z /nat_of_P /Pmult_nat /=.
Qed.

Lemma neq0_when_pos (r : rat) : 0 < r -> r != 0.
Proof.  rewrite lt0r.  case/andP.  done.  Qed.

(* Move these and the previous one to rat_pos? *)
Lemma affine_poly_pos (n : int) (a b : rat) :
  0 <= n -> a > 0 -> b > 0 -> 0 < a * n%:~R + b.
Proof.
move=> le_0_n pos_a pos_b.
apply: (@lt_le_trans _ _ b) => //.
rewrite ler_addr mulr_ge0 //.
  by rewrite le0r pos_a orbT.
by rewrite ler0z.
Qed.

Lemma affine_poly_pos_with_one (n : int) (b : rat) :
  0 <= n -> b > 0 -> 0 < n%:~R + b.
Proof.
move=> ? ?.
have <- : rat_of_Z 1 * n%:~R = n%:~R by rewrite rat_of_ZEdef mul1r.
apply: affine_poly_pos => //.
by rewrite rat_of_ZEdef.
Qed.
