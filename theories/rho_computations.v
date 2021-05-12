Require Import BinInt.
Require Import NArith.

From mathcomp Require Import all_ssreflect all_algebra.
Require Import rat_of_Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From CoqEAL Require Import hrel param refinements.
From CoqEAL Require Import pos binnat binint rational.
Import Refinements (* AlgOp *). 

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope ring_scope.

(* You don't really need Z here but positive *)
Definition rat_of_positive_fun (p : positive) : rat :=
  (pos_to_int (Op.spec p))%:~R.

Definition rat_of_positive_ := nosimpl rat_of_positive_fun.

Module Type RatOfZSig.
Parameter rat_of_positive : positive -> rat.
Axiom rat_of_positiveEdef : rat_of_positive = rat_of_positive_.
End RatOfZSig.

Module rat_of_positiveDef : RatOfZSig.
Definition rat_of_positive : positive -> rat := rat_of_positive_fun.
Definition rat_of_positiveEdef := erefl rat_of_positive.
End rat_of_positiveDef.

Export rat_of_positiveDef.

(* FIXME : For the time being, we work with two casts but we should keep *)
(* only one in the end. *)

Lemma rat_of_Z_rat_of_positive (p : positive) :
  rat_of_Z (Z.pos p)%Z = rat_of_positive p.
Proof.
rewrite rat_of_positiveEdef rat_of_ZEdef /rat_of_Z_ /rat_of_Z_fun.
rewrite /rat_of_positive_ /rat_of_positive_fun /pos_to_int /=.
by rewrite val_insubd to_nat_gt0 natz.
Qed.

Lemma rat_of_positiveE (p : positive) : 
  rat_of_positive p = (Posz (nat_of_P p))%:~R.
Proof. by rewrite -rat_of_Z_rat_of_positive rat_of_ZEdef. Qed.

Fact lt_0_rat_of_positive (p : positive) : 0 < rat_of_positive p.
Proof.
rewrite rat_of_positiveEdef /rat_of_positive_ /rat_of_positive_fun /pos_to_int.
by rewrite val_insubd to_nat_gt0 natz ltr0n to_nat_gt0.
Qed.

(* Generic programming of your functions : *)
(* we abstract wrt Q and all the operations you use *)
Section generic.
Import Refinements.
Import Op.

(* In the future, many of these might come packaged together *)
Context (AQ : Type).
Context (zeroAQ : zero_of AQ).
Context (addAQ : add_of AQ) (oppAQ : opp_of AQ) (subAQ : sub_of AQ).
Context (divAQ : div_of AQ) (mulAQ : mul_of AQ) (expAQ : exp_of AQ nat).
Context (positive_toAQ : cast_of positive AQ).
Context (nat_to_AQ : cast_of nat AQ).

Local Open Scope computable_scope.

Definition generic_beta (i : AQ) : AQ := 
  ((i + cast 1%positive) %/ (i + cast 2%positive)) ^ 3.

Definition generic_alpha (i : AQ) : AQ :=
     (cast 17%positive * i ^ 2 + cast 51%positive * i + cast 39%positive)
   * (cast 2%positive * i + cast 3%positive) %/ (i + cast 2%positive) ^ 3.

Definition generic_h (i : AQ) (x : AQ) := generic_alpha i  - generic_beta i %/ x.

Fixpoint generic_h_iter (n : nat) : AQ := 
  match n with
    | 0 => 0%C
    | 1 => 0%C
    | 2 => cast 1445%positive %/ cast 73%positive
    | m.+1 => let mz := cast m in
              let res_m := generic_h_iter m in
              generic_h mz res_m
  end.

End generic.

Definition subr {R : zmodType} (x y : R) : R := x - y.
Definition divr {R : unitRingType} (x y : R) : R := x / y.
Definition natr {R : ringType} (x : nat) : R := x%:R.

Definition alpha := 
  @generic_alpha rat +%R divr *%R (@GRing.exp _) rat_of_positive.

Definition beta := @generic_beta rat +%R divr (@GRing.exp _) rat_of_positive.

Definition h := 
  @generic_h rat +%R subr divr *%R (@GRing.exp _) rat_of_positive.

Definition  h_iter :=
  @generic_h_iter rat 0%R +%R subr divr *%R (@GRing.exp _) rat_of_positive natr.

(* This is the "free" part of the refinements: *)
(* Parametricity of the previously operations.  For now our library
   provides a semi-automated resolution based on typeclasses. We aim
   to replace it by an ML plugin in Chantal Keller and Marc Lasson
   style so that it is as "free" in the implementation as it is in
   theory. *)
Section parametric.
Import Refinements.
Import Op.

Context (AQ : Type).
Context (zeroAQ : zero_of AQ) (addAQ : add_of AQ) (oppAQ : opp_of AQ) (subAQ : sub_of AQ).
Context (divAQ : div_of AQ) (mulAQ : mul_of AQ) (expAQ : exp_of AQ nat).
Context (ZtoAQ : cast_of positive AQ) (nat_to_AQ : cast_of nat AQ).
Context (RAQ : rat -> AQ -> Type).
Context (RzeroAQ : refines RAQ 0%R zero_op).
Context (RaddAQ : refines (RAQ ==> RAQ ==> RAQ)%rel +%R add_op).
Context (RoppAQ : refines (RAQ ==> RAQ)%rel -%R opp_op).
Context (RsubAQ : refines (RAQ ==> RAQ ==> RAQ)%rel subr sub_op).
Context (RmulAQ : refines (RAQ ==> RAQ ==> RAQ)%rel *%R mul_op).
Context (RdivAQ : refines (RAQ ==> RAQ ==> RAQ)%rel divr div_op).
Context (RexpAQ : refines (RAQ ==> Logic.eq ==> RAQ)%rel (@GRing.exp _) exp_op).
Context (RZtoAQ : refines (Logic.eq ==> RAQ)%rel rat_of_positive cast).
Context (Rnat_to_AQ : refines (Logic.eq ==> RAQ)%rel natr cast).

Local Instance eq_refines T (x : T) : refines Logic.eq x x.
Proof. by rewrite refinesE. Qed.

Parametricity positive.
Parametricity generic_beta.
Parametricity generic_alpha.
Parametricity generic_h.
Parametricity generic_h_iter.

Global Instance refines_bool_eq x y : refines positive_R x y -> refines eq x y.
Proof. by rewrite !refinesE; elim => // p q _ ->. Qed.

Global Instance refines_beta :
  refines (RAQ ==> RAQ)%rel beta (generic_beta _ _ _ _).
Proof. by param generic_beta_R. Qed.

Global Instance refines_alpha :
  refines (RAQ ==> RAQ)%rel alpha (generic_alpha _ _ _ _ _).
Proof. by param generic_alpha_R. Qed.

Global Instance refines_h :
  refines (RAQ ==> RAQ ==> RAQ)%rel h (generic_h _ _ _ _ _ _).
Proof. by param generic_h_R. Qed.

Global Instance refines_h_iter n :
  refines (RAQ)%rel (h_iter n) (generic_h_iter _ _ _ _ _ _ _ _ n).
Proof. by param generic_h_iter_R; rewrite refinesE; elim: n => //= *; constructor. Qed.

End parametric.

Section result.

Notation Q  := (Q (Z N positive) positive).
Notation RQ := (RratC (RZNP Rnat Rpos) Rpos).

(* A few things to get the compatibility between
   the CoqEAL library and your local requirements *)
Section extra_refinements.

Global Instance Q_of_nat : Op.cast_of nat Q :=
  fun n => iter n (Op.add_op 1%C) 0%C.

Global Instance RQ_of_nat : refines (Logic.eq ==> RQ)%rel natr cast.
Proof.
eapply refines_abstr => n b; rewrite refinesE => <- {b}.
rewrite /natr /cast /Q_of_nat /=.
elim: n => [|n ihn] //=; first by rewrite mulr0n; tc.
by rewrite mulrS; tc.
Qed.

Global Instance RQ_of_pos :
  refines (Logic.eq ==> RQ)%rel rat_of_positive cast.
Proof.
eapply refines_abstr => n b; rewrite refinesE => <- {b}.
rewrite rat_of_positiveEdef /rat_of_positive_ /rat_of_positive_fun.
by rewrite /cast /cast_PQ; tc.
Qed.

Global Instance positive_refines_eq (x : positive) : refines Logic.eq x x.
Proof. by rewrite refinesE. Qed. 

Global Instance refines_eq_nat_R_spec :
  refines (eq ==> nat_R)%rel Op.spec_id id.
Proof. by rewrite refinesE=> ? ? ->; apply: nat_Rxx. Qed.

End extra_refinements.
End result.
