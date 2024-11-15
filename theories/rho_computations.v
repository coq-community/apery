Require Import BinInt.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint rat.
From CoqEAL Require Import hrel param refinements.
From CoqEAL Require Import pos binnat rational.
Require Import tactics rat_of_Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Delimit Scope Z_scope with coqZ.

Section Z_theory.
Import Refinements.Op.

Global Instance zeroZ : zero_of Z := 0%coqZ.
Global Instance oneZ : one_of Z := 1%coqZ.
Global Instance addZ : add_of Z := Z.add.
Global Instance oppZ : opp_of Z := Z.opp.
Global Instance subZ : sub_of Z := Z.sub.
Global Instance mulZ : mul_of Z := Z.mul.
Global Instance expZ : exp_of Z N :=
  fun x y => if y is Npos p then Z.pow_pos x p else 1%coqZ.
Global Instance eqZ : eq_of Z := Z.eqb.
Global Instance leqZ : leq_of Z := Z.leb.
Global Instance ltZ : lt_of Z := Z.ltb.
Global Instance cast_NZ : cast_of N Z := Z.of_N.
Global Instance cast_PZ : cast_of positive Z := Zpos.
Global Instance cast_ZN : cast_of Z N := Z.to_N.
Global Instance cast_ZP : cast_of Z positive := Z.to_pos.
Global Instance specZ : spec_of Z int := int_of_Z.
Global Instance implemZ : implem_of int Z := Z_of_int.

Local Open Scope rel_scope.

Definition Rint : int -> Z -> Type := fun_hrel int_of_Z.

Lemma RintE n x : refines Rint n x -> n = int_of_Z x.
Proof. by rewrite refinesE. Qed.

Global Instance Rint_0 : refines Rint 0 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rint_1 : refines Rint 1 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rint_add : refines (Rint ==> Rint ==> Rint) +%R +%C.
Proof. by rewrite refinesE => _ ? <- _ ? <-; rewrite -rmorphD. Qed.

Global Instance Rint_opp : refines (Rint ==> Rint) -%R -%C.
Proof. by rewrite refinesE => _ ? <-; rewrite -rmorphN. Qed.

Global Instance Rint_sub :
  refines (Rint ==> Rint ==> Rint) (fun x y => x - y) sub_op.
Proof. by rewrite refinesE => _ ? <- _ ? <-; rewrite -rmorphB. Qed.

Global Instance Rint_mul : refines (Rint ==> Rint ==> Rint) *%R *%C.
Proof. by rewrite refinesE => _ ? <- _ ? <-; rewrite -rmorphM. Qed.

Global Instance Rint_exp :
  refines (Rint ==> Rnat ==> Rint) (@GRing.exp _) exp_op.
Proof.
rewrite refinesE /Rint /Rnat /fun_hrel /exp_op /expZ => _ ? <- _ [|?] <-; lia.
Qed.

Global Instance Rint_eq : refines (Rint ==> Rint ==> bool_R) eqtype.eq_op eq_op.
Proof.
rewrite refinesE => _ x <- _ y <-.
have ->: (int_of_Z x == int_of_Z y)%R = Z.eqb x y by lia.
exact: bool_Rxx.
Qed.

Global Instance Rint_leq : refines (Rint ==> Rint ==> bool_R) Num.le leq_op.
Proof.
rewrite refinesE => _ x <- _ y <-.
have ->: (int_of_Z x <= int_of_Z y)%R = Z.leb x y by lia.
exact: bool_Rxx.
Qed.

Global Instance Rint_lt : refines (Rint ==> Rint ==> bool_R) Num.lt lt_op.
Proof.
rewrite refinesE => _ x <- _ y <-.
have ->: (int_of_Z x < int_of_Z y)%R = Z.ltb x y by lia.
exact: bool_Rxx.
Qed.

Global Instance Rint_Posz : refines (Rnat ==> Rint) Posz cast.
Proof. by rewrite refinesE /Rint /fun_hrel /cast /cast_NZ => _ ? <-; lia. Qed.

Global Instance Rint_pos_to_int : refines (Rpos ==> Rint) pos_to_int cast.
Proof.
rewrite refinesE /Rint /fun_hrel /cast /cast_PZ => _ ? <-.
by rewrite /pos_to_int val_insubd; case: ifP; lia.
Qed.

Global Instance Rint_int_to_nat : refines (Rint ==> Rnat) int_to_nat cast.
Proof.
rewrite refinesE /Rnat /fun_hrel /cast /cast_ZN /int_to_nat => _ ? <-.
case: ifP; lia.
Qed.

Global Instance Rint_int_to_pos : refines (Rint ==> Rpos) int_to_pos cast.
Proof.
rewrite refinesE /Rpos /fun_hrel /cast /cast_ZP /int_to_pos /int_to_nat.
have H0: pos_of_positive 1 = insubd pos1 0%N.
  by rewrite /insubd; apply: canLR positive_of_posK _; case: insubP.
by move=> _ [|p|p] <- //=; case: ifP; last lia.
Qed.

Global Instance Rint_specZ_r x : refines Rint (spec x) x.
Proof. by rewrite refinesE /Rint /fun_hrel; case: x => /=; lia. Qed.

Global Instance Rint_specZ_l : refines (Rint ==> Logic.eq) spec_id spec.
Proof. by rewrite refinesE => _ ? <-. Qed.

Global Instance Rint_implem : refines (Logic.eq ==> Rint) implem_id implem.
Proof.
by rewrite refinesE /Rint /fun_hrel => ? _ <-; rewrite [LHS]Z_of_intK.
Qed.

End Z_theory.

(* Generic programming of your functions : *)
(* we abstract wrt Q and all the operations you use *)
Section generic.
Import Refinements.Op.

(* In the future, many of these might come packaged together *)
Context (AQ : Type).
Context (zeroAQ : zero_of AQ).
Context (addAQ : add_of AQ) (oppAQ : opp_of AQ) (subAQ : sub_of AQ).
Context (divAQ : div_of AQ) (mulAQ : mul_of AQ) (expAQ : exp_of AQ nat).
Context (Z_toAQ : cast_of Z AQ) (nat_to_AQ : cast_of nat AQ).

Local Open Scope computable_scope.

Definition generic_beta (i : AQ) : AQ := 
  ((i + cast 1%coqZ) %/ (i + cast 2%coqZ)) ^ 3%N.

Definition generic_alpha (i : AQ) : AQ :=
     (cast 17%coqZ * i ^ 2%N + cast 51%coqZ * i + cast 39%coqZ)
   * (cast 2%coqZ * i + cast 3%coqZ) %/ (i + cast 2%coqZ) ^ 3%N.

Definition generic_h (i : AQ) (x : AQ) := generic_alpha i  - generic_beta i %/ x.

Fixpoint generic_h_iter (n : nat) : AQ := 
  match n with
    | 0 => 0%C
    | 1 => 0%C
    | 2 => cast 1445%coqZ %/ cast 73%coqZ
    | m.+1 => let mz := cast m in
              let res_m := generic_h_iter m in
              generic_h mz res_m
  end.

End generic.

Definition subr {R : zmodType} (x y : R) : R := x - y.
Definition divr {R : unitRingType} (x y : R) : R := x / y.
Definition natr {R : ringType} (x : nat) : R := x%:R.

Definition alpha := @generic_alpha rat +%R divr *%R (@GRing.exp _) rat_of_Z.

Definition beta := @generic_beta rat +%R divr (@GRing.exp _) rat_of_Z.

Definition h := 
  @generic_h rat +%R subr divr *%R (@GRing.exp _) rat_of_Z.

Definition  h_iter :=
  @generic_h_iter rat 0%R +%R subr divr *%R (@GRing.exp _) rat_of_Z natr.

(* This is the "free" part of the refinements: *)
(* Parametricity of the previously operations.  For now our library
   provides a semi-automated resolution based on typeclasses. We aim
   to replace it by an ML plugin in Chantal Keller and Marc Lasson
   style so that it is as "free" in the implementation as it is in
   theory. *)
Section parametric.
Import Refinements.Op.

Context (AQ : Type).
Context (zeroAQ : zero_of AQ) (addAQ : add_of AQ) (oppAQ : opp_of AQ) (subAQ : sub_of AQ).
Context (divAQ : div_of AQ) (mulAQ : mul_of AQ) (expAQ : exp_of AQ nat).
Context (ZtoAQ : cast_of Z AQ) (nat_to_AQ : cast_of nat AQ).
Context (RAQ : rat -> AQ -> Type).
Context (RzeroAQ : refines RAQ 0%R zero_op).
Context (RaddAQ : refines (RAQ ==> RAQ ==> RAQ)%rel +%R add_op).
Context (RoppAQ : refines (RAQ ==> RAQ)%rel -%R opp_op).
Context (RsubAQ : refines (RAQ ==> RAQ ==> RAQ)%rel subr sub_op).
Context (RmulAQ : refines (RAQ ==> RAQ ==> RAQ)%rel *%R mul_op).
Context (RdivAQ : refines (RAQ ==> RAQ ==> RAQ)%rel divr div_op).
Context (RexpAQ : refines (RAQ ==> Logic.eq ==> RAQ)%rel (@GRing.exp _) exp_op).
Context (RZtoAQ : refines (Logic.eq ==> RAQ)%rel rat_of_Z cast).
Context (Rnat_to_AQ : refines (Logic.eq ==> RAQ)%rel natr cast).

Parametricity positive.
Parametricity Z.
Parametricity generic_beta.
Parametricity generic_alpha.
Parametricity generic_h.
Parametricity generic_h_iter.

Global Instance refines_bool_eq x y : refines Z_R x y -> refines eq x y.
Proof. by rewrite !refinesE; case => // p q; elim => // ? ? _ [->]. Qed.

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

Notation Q  := (Q Z positive).
Notation RQ := (RratC Rint Rpos).

(* A few things to get the compatibility between
   the CoqEAL library and your local requirements *)
Section extra_refinements.
Import Refinements.Op.

Global Instance Q_of_nat : cast_of nat Q := fun n : nat => (Z_of_int n, 1%C).
Global Instance Q_of_int : cast_of int Q := fun n : int => (Z_of_int n, 1%C).

Global Instance RQ_of_nat : refines (Logic.eq ==> RQ)%rel natr cast.
Proof.
rewrite !refinesE => x _ <- /=; exists (Posz x, 1%C).
rewrite /Rrat /Rint /Rpos /fun_hrel [LHS]divr1 /=.
by split; last split; [| lia | exact: canLR positive_of_posK _].
Qed.

Global Instance RQ_of_int : refines (Logic.eq ==> RQ)%rel intr cast.
Proof.
rewrite !refinesE => x _ <- /=; exists (x, 1%C).
rewrite /Rrat /Rint /Rpos /fun_hrel [LHS]divr1 /=.
by split; last split; [| lia | exact: canLR positive_of_posK _].
Qed.

Global Instance RQ_of_Z : refines (Logic.eq ==> RQ)%rel rat_of_Z cast.
Proof.
rewrite !refinesE => x _ <- /=; exists (int_of_Z x, 1%C).
rewrite rat_of_ZEdef /Rrat /Rint ?Rpos /fun_hrel [LHS]divr1 /=.
by split; last split; [| lia | exact: canLR positive_of_posK _].
Qed.

Global Instance Z_refines_eq (x : Z) : refines Logic.eq x x.
Proof. by rewrite refinesE. Qed.

Global Instance refines_eq_nat_R_spec : refines (eq ==> nat_R)%rel spec_id id.
Proof. by rewrite refinesE=> ? ? ->; apply: nat_Rxx. Qed.

End extra_refinements.
End result.
