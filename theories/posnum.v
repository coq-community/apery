(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
(* Require Import Reals. *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint all_field.
(* Require Import boolp reals. *)

(******************************************************************************)
(* This file develops tools to make the manipulation of positive numbers      *)
(* easier, thanks to canonical structures.                                    *)
(*                                                                            *)
(*          !! x == triggers pretyping to fill the holes of the term x. The   *)
(*                  main use case is to trigger typeclass inference in the    *)
(*                  body of a ssreflect have := !! body.                      *)
(*                  Credits: Enrico Tassi.                                    *)
(*    {posnum R} == interface type for elements in R that are positive; R     *)
(*                  must have a numDomainType structure.                      *)
(*                  Allows to solve automatically goals of the form x > 0 if  *)
(*                  x is canonically a {posnum R}. {posnum R} is canonically  *)
(*                  stable by addition, multiplication, inverse, min and sqrt *)
(*                  All positive natural numbers ((n.+1)%:R) are also         *)
(*                  canonically in {posnum R}                                 *)
(*   PosNum xgt0 == packs the proof xgt0 : x > 0, for x : R, to build a       *)
(*                  {posnum R}.                                               *)
(*        x%:pos == explicitely casts x to {posnum R}, triggers the inference *)
(*                  of a {posnum R} structure for x.                          *)
(*        x%:num == explicit cast from {posnum R} to R.                       *)
(*       posreal == notation for {posnum R}, where R is the type of real      *)
(*                  numbers.                                                  *)
(*             2 == notation for 2%:R.                                        *)
(*    [gt0 of x] == infers a {posnum R} structure for x and outputs the proof *)
(*                  that x is positive.                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

(* Enrico's trick for tc resolution in have *)
(* Notation "!! x" := (ltac:(refine x)) (at level 100, only parsing). *)
(* infer class to help typeclass inference on the fly *)
Class infer (P : Prop) := Infer : P.
(* Hint Mode infer ! : typeclass_instances. *)
#[export] Hint Extern 0 (infer _) => (exact) : typeclass_instances.
Lemma inferP (P : Prop) : P -> infer P. Proof. by []. Qed.

Lemma splitr (R : numFieldType) (x : R) : x = x / 2%:R + x / 2%:R.
Proof. by rewrite -mulr2n -[RHS]mulr_natr mulfVK //= pnatr_eq0. Qed.

Record posnum_def (R : numDomainType) := PosNumDef {
  num_of_pos :> R;
  posnum_gt0 : num_of_pos > 0
}.
#[export] Hint Resolve posnum_gt0 : core.
#[export] Hint Extern 0 ((0 < _)%R = true) => exact: posnum_gt0 : core.
Definition posnum_of (R : numDomainType) (phR : phant R) := posnum_def R.
Identity Coercion posnum_of_id : posnum_of >-> posnum_def.
Notation "'{posnum' R }" := (posnum_of (@Phant R))
  (at level 0, format "'{posnum'  R }").
Definition PosNum (R : numDomainType) x x_gt0 : {posnum R} :=
  @PosNumDef _ x x_gt0.

Definition pos_of_num (R : numDomainType) (x : {posnum R})
   (phx : phantom R x) := x.
Notation "x %:pos" := (pos_of_num (Phantom _ x))
  (at level 0, format "x %:pos") : ring_scope.
Notation "x %:num" := (num_of_pos x)
  (at level 0, format "x %:num") : ring_scope.

From mathcomp Require Import algC.

Notation posalgc := {posnum algC}.
(* Notation "2" := 2%:R : ring_scope. *)

Section PosNum.
Context {R : numDomainType}.
Implicit Types (x y : {posnum R}).

Definition posnum_gt0_def x (phx : phantom R x) := posnum_gt0 x.

Lemma posnum_ge0 x : x >= 0 :> R. Proof. by apply: ltW. Qed.
Lemma posnum_eq0 x : (x == 0 :> R) = false. Proof. by rewrite gt_eqF. Qed.
Lemma posnum_neq0 x : (x != 0 :> R). Proof. by rewrite gt_eqF. Qed.

Lemma add_pos_gt0 x y : 0 < x%:num + y%:num.
Proof. by rewrite addr_gt0. Qed.
Canonical addr_posnum x y := PosNum (add_pos_gt0 x y).

Lemma mul_pos_posnum x y : 0 < x%:num * y%:num.
Proof. by rewrite mulr_gt0. Qed.
Canonical mulr_posnum x y := PosNum (mul_pos_posnum x y).

Lemma muln_pos_posnum x n : 0 < x%:num *+ n.+1.
Proof. by rewrite pmulrn_lgt0. Qed.
Canonical mulrn_posnum x n := PosNum (muln_pos_posnum x n).

Lemma inv_pos_gt0 x : 0 < x%:num^-1. Proof. by rewrite invr_gt0. Qed.
Canonical invr_posnum x := PosNum (inv_pos_gt0 x).

Lemma pos_Sn (n : nat) : 0 < n.+1%:R :> R.
Proof. by []. Qed.
Canonical Sn_posnum n := PosNum (pos_Sn n).

Lemma posnumSz (n : nat) : 0 < n.+1%:~R :> R.
Proof. by rewrite ltr0z. Qed.
Canonical intSn_posnum n := PosNum (posnumSz n).

Lemma posnum_expn (n : nat) x : 0 < x%:num ^+ n.
Proof. by rewrite exprn_gt0. Qed.
Canonical posum_expn n x := PosNum (posnum_expn n x).

Lemma posnum_factn (n : nat) : 0 < n`!%:~R :> R.
Proof. rewrite ltr0z; exact: fact_gt0. Qed.
Canonical posum_factn n := PosNum (posnum_factn n).


Lemma one_pos_gt0 : 0 < 1 :> R. Proof. by rewrite ltr01. Qed.
Canonical oner_posnum := PosNum one_pos_gt0.

End PosNum.
#[export] Hint Extern 0 ((0 <= _)%R = true) => exact: posnum_ge0 : core.
#[export] Hint Extern 0 ((_ != 0)%R = true) => exact: posnum_neq0 : core.

Section PosNumReal.
Context {R : realDomainType}.
Implicit Types (x y : {posnum R}).

Lemma posnum_le0 x : (x%:num <= 0 :> R) = false.
Proof. by rewrite leNgt posnum_gt0. Qed.
Lemma posnum_lt0 x : (x%:num < 0 :> R) = false.
Proof. by rewrite ltNge posnum_ge0. Qed.

Lemma min_pos_gt0 x y : 0 < minr x%:num y%:num.
Proof. by rewrite lt_min !posnum_gt0. Qed.
Canonical minr_posnum x y := PosNum (@min_pos_gt0 x y).

End PosNumReal.

Lemma sqrt_pos_gt0 (R : rcfType) (x : {posnum R}) : 0 < Num.sqrt x%:num.
Proof. by rewrite sqrtr_gt0. Qed.
Canonical sqrt_posnum (R : rcfType) (x : {posnum R}) := PosNum (sqrt_pos_gt0 x).

Variant posnum_spec (R : numDomainType) (x : R) :
  R -> bool -> bool -> bool -> Type :=
| IsPosnum (p : {posnum R}) : posnum_spec x (p : R) false true true.

Lemma posnumP (R : numDomainType) (x : R) : 0 < x ->
  posnum_spec x x (x == 0) (0 <= x) (0 < x).
Proof.
move=> x_gt0; case: real_ltgt0P (x_gt0) => []; rewrite ?gtr0_real // => _ _.
by rewrite -[x]/(PosNum x_gt0)%:num; constructor.
Qed.

#[export] Hint Resolve posnum_gt0 : core.
#[export] Hint Resolve posnum_ge0 : core.
#[export] Hint Resolve posnum_neq0 : core.
Notation "[gt0 'of' x ]" := (posnum_gt0_def (Phantom algC x))
 (format "[gt0 'of'  x ]").
