From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun bigop order ssralg ssrnum ssrint.
From mathcomp Require Export zify ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Ltac Zify.zify_post_hook ::=
  zify_ssreflect.SsreflectZifyInstances.divZ_modZ_to_equations.

Structure zifyRing (R : ringType) :=
  ZifyRing { rval : R; zval : int; _ : rval = zval%:~R }.

Arguments ZifyRing [R] rval zval _.

Module Import Internals.

Section Ring.

Variable R : ringType.
Notation zifyRing := (zifyRing R).
Notation ZifyRing := (@ZifyRing R).
Notation rval := (@rval R).
Notation zval := (@zval R).

Lemma zifyRingE (e : zifyRing) : rval e = (zval e)%:~R. Proof. by case: e. Qed.

Definition zify_zero := ZifyRing 0 0 erefl.

Lemma zify_opp_subproof e1 : - rval e1 = (- zval e1)%:~R.
Proof. by rewrite zifyRingE mulrNz. Qed.

Definition zify_opp e1 :=
  ZifyRing (- rval e1) (- zval e1) (zify_opp_subproof e1).

Lemma zify_add_subproof e1 e2 : rval e1 + rval e2 = (zval e1 + zval e2)%:~R.
Proof. by rewrite 2!zifyRingE intrD. Qed.

Definition zify_add e1 e2 :=
  ZifyRing (rval e1 + rval e2) (zval e1 + zval e2) (zify_add_subproof e1 e2).

Lemma zify_mulrz_subproof e1 n : rval e1 *~ n = (zval e1 *~ n)%:~R.
Proof. by rewrite zifyRingE -mulrzA -mulrzz. Qed.

Definition zify_mulrn e1 n :=
  ZifyRing (rval e1 *+ n) (zval e1 *+ n) (zify_mulrz_subproof e1 n).

Definition zify_mulrz e1 n :=
  ZifyRing (rval e1 *~ n) (zval e1 *~ n) (zify_mulrz_subproof e1 n).

Definition zify_one := ZifyRing 1 1 erefl.

Lemma zify_mul_subproof e1 e2 : rval e1 * rval e2 = (zval e1 * zval e2)%:~R.
Proof. by rewrite 2!zifyRingE intrM. Qed.

Definition zify_mul e1 e2 :=
  ZifyRing (rval e1 * rval e2) (zval e1 * zval e2) (zify_mul_subproof e1 e2).

Lemma zify_exprn_subproof e1 n : rval e1 ^+ n = (zval e1 ^+ n)%:~R.
Proof. by rewrite zifyRingE; elim: n => //= n; rewrite !exprS intrM => ->. Qed.

Definition zify_exprn e1 n :=
  ZifyRing (rval e1 ^+ n) (zval e1 ^+ n) (zify_exprn_subproof e1 n).

End Ring.

Lemma zify_eqb (R : numDomainType) (e1 e2 : zifyRing R) :
  (rval e1 == rval e2) = (zval e1 == zval e2).
Proof. by rewrite 2!zifyRingE eqr_int. Qed.

Lemma zify_ler (R : numDomainType) (e1 e2 : zifyRing R) :
  (rval e1 <= rval e2) = (zval e1 <= zval e2).
Proof. by rewrite 2!zifyRingE ler_int. Qed.

Lemma zify_ltr (R : numDomainType) (e1 e2 : zifyRing R) :
  (rval e1 < rval e2) = (zval e1 < zval e2).
Proof. by rewrite 2!zifyRingE ltr_int. Qed.

End Internals.

Lemma rpred_zify (R : ringType) (S : {pred R}) (ringS : subringPred S)
                 (kS : keyed_pred ringS) (e : zifyRing R) : rval e \in kS.
Proof. by rewrite zifyRingE rpred_int. Qed.

Canonical zify_zero.
Canonical zify_opp.
Canonical zify_add.
Canonical zify_mulrn.
Canonical zify_mulrz.
Canonical zify_one.
Canonical zify_mul.
Canonical zify_exprn.

Ltac zify_ring_hyp :=
  let b := fresh "b" in
  match goal with
  | H : context [ eq_op ] |- _ =>
    set b := _ == _ in H; zify_ring_hyp;
    rewrite 1?[b]zify_eqb {}/b [_ == _]/= in H
  | H : context [ <=%O ] |- _ =>
    set b := _ <= _ in H; zify_ring_hyp;
    rewrite 1?[b]zify_ler {}/b [_ <= _]/= in H
  | H : context [ <%O ] |- _ =>
    set b := _ < _ in H; zify_ring_hyp;
    rewrite 1?[b]zify_ltr {}/b [_ < _]/= in H
  | _ => idtac
  end.

Ltac zify_ring_goal :=
  let b := fresh "b" in
  match goal with
  | |- context [ eq_op ] =>
    set b := _ == _; zify_ring_goal; rewrite 1?[b]zify_eqb {}/b [_ == _]/=
  | |- context [ <=%O ] =>
    set b := _ <= _; zify_ring_goal; rewrite 1?[b]zify_ler {}/b [_ <= _]/=
  | |- context [ <%O ] =>
    set b := _ < _;  zify_ring_goal; rewrite 1?[b]zify_ltr {}/b [_ < _]/=
  | _ => idtac
  end.

Ltac zify_ring := zify_ring_hyp; zify_ring_goal.

Ltac ring_lia := zify_ring; lia.
Ltac ring_nia := zify_ring; nia.
