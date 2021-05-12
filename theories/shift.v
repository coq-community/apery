From mathcomp Require Import all_ssreflect all_algebra. 

(* Tentative definition of shifts for indexes of sequences. *)
(* Expressions featuring shifts can be converted into their analogues
   in terms of additions of integers (resp. integers embedded in a
   ring type) using the (multi-)rewriting rule shift2Z
   (resp. shift2R). *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope ring_scope.

Module int.

Section shift.

Definition shift1 (z : int) := z + 1.

Definition shift_ n := iter n shift1.

Definition shift := nosimpl shift_.


Lemma shiftE : shift = shift_. by []. Qed.

(* Rewriting lemmas to get rid of the shifts in rational fractions.
   These steps cannot be internalized in the rat_field
   pre-transformation since their justification requires more than
   conversion. *)

Lemma shift1E z : shift1 z = z + 1.
Proof. by []. Qed.

Lemma zshiftP z m : shift m z = z + m.
Proof.
elim: m => [| m ihm]; first by rewrite addr0.
by rewrite shiftE /= -shiftE ihm -addn1 PoszD addrA.
Qed.

(* A multirule to convert both shift and shift1 into int expressions
   in one shot.  I cannot find a better solution for now. *)
Definition shift2Z := (zshiftP, shift1E).

Lemma shiftP (R : ringType) z m : (shift m z)%:~R = z%:~R + m%:~R :> R.
Proof. by rewrite zshiftP rmorphD. Qed.

Lemma shift1P (R : ringType) z : (shift1 z)%:~R = z%:~R + 1 :> R.
Proof. by rewrite rmorphD. Qed.

(* A multirule to convert both shift and shift1 into ring expressions
   in one shot.  I cannot find a better solution for now. *)
Definition shift2R := (shiftP, shift1P).

Lemma shift0 z : shift 0 z = z.
Proof. by rewrite shiftE. Qed.

Lemma shiftS z m : shift 1 (shift m z) = shift m.+1 z.
Proof. by rewrite shiftE /=. Qed.

End shift.

End int.

