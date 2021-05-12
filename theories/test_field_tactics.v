Require Import ZArith.
Require Import Field.

From mathcomp Require Import all_ssreflect all_algebra.
Require Import field_tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope ring_scope.

(* rat_of_Z being locked, we cannot prove this with prefield only *)
Lemma testZ0 : ((rat_of_Z Z0) + (rat_of_Z 0)) = 0.
rat_field.
Qed.

(* rat_of_Z being locked, we cannot prove this with prefield only *)
Lemma testZ3 : ((rat_of_Z 3) + (rat_of_Z 3)) = (rat_of_Z 6).
rat_field.
Qed.

(* rat_of_Z being locked, we cannot prove this with prefield only *)
Lemma testZ3000 : 2%:~R * (rat_of_Z 3001) = (rat_of_Z 6002).
rat_field.
Qed.


Lemma test_one : 1 = 1 :> rat.
prefield; reflexivity.
Qed.

Lemma test_zero : 0 = 0 :> rat.
prefield; reflexivity.
Qed.

Lemma test_op (n : rat) : - n = - n :> rat.
prefield; reflexivity.
Qed.

Lemma test_inv (n : rat) : n ^-1 = n ^-1 :> rat.
prefield; reflexivity.
Qed.

Lemma test_add (n m : rat) : (n + m) = n + m :> rat.
prefield; reflexivity.
Qed.

Lemma test_mul (n m : rat) : (n * m) = n * m :> rat.
prefield; reflexivity.
Qed.

Lemma test_mul_add (n m : rat) : (n * (m + n)) = (n * (m + n)) :> rat.
prefield; reflexivity.
Qed.

Lemma test_cst : (Posz 5)%:~R = (Posz 5)%:~R :> rat.
prefield; reflexivity.
Qed.

Lemma test_pow0 (n : rat) : n ^ (Posz 0) = 1.
prefield; reflexivity.
Qed.

Lemma test_pow1 (n : rat) : n ^ (Posz 1) = n.
prefield; reflexivity.
Qed.

Lemma test_pow (n : rat) : n ^ (Posz 2) = n * n.
prefield; reflexivity.
Qed.


Lemma test_one_int : 1%:~R = 1%:~R :> rat.
prefield; reflexivity.
Qed.

Lemma test_zero_int : 0%:~R = 0%:~R :> rat.
prefield; reflexivity.
Qed.

(* Here we need the rewrite first*)
Lemma test_op_int (n : int) : (- n)%:~R = (- n)%:~R :> rat.
by rewrite rmorphN; rat_field.
Qed.

(* WARNING : no support needed for divisibility on int!
Lemma test_inv_int (n : int) : (n^-1)%:~R = (n^-1)%:~R :> rat.
Admitted.
*)

Lemma test_add_int (n m : int) : (n + m)%:~R = (n + m)%:~R :> rat.
by rewrite rmorphD; rat_field.
Qed.

Lemma test_mul_int (n m : int) : (n * m)%:~R = (n * m)%:~R :> rat.
by rewrite rmorphM; rat_field.
Qed.

Lemma test_mul_add_int (n m : int) :
  (n * (m + n))%:~R = (n * (m + n))%:~R :> rat.
by rewrite rmorphM rmorphD; rat_field.
Qed.

Lemma test_pow0_int (n : int) : (n ^(Posz 0))%:~R = 1 :> rat.
by rat_field.
Qed.

Lemma test_pow_int (n : int) : (n ^(Posz 2))%:~R = powq n%:~R 2 :> rat.
Proof. 
rewrite -exprz_pintl; last by done.
by prefield.
Qed.

(* rat_field works because it is in fact a reflexivity. *)
Lemma test_pow_add_int (n m : int) :
  ((n + m) ^(Posz 2))%:~R = ((n + m) ^(Posz 2))%:~R :> rat.
by rat_field => //.
Qed.

Lemma test_opp_add (n m : int) : - ((n + m)%:~R) = - ((n + m)%:~R) :> rat.
by rat_field; rewrite // rmorphD.
Qed.

