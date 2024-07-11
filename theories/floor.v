From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Lemma floorQ_spec (r : rat) : (Num.floor r)%:Q <= r < (Num.floor r)%:Q + 1.
Proof. by rewrite ge_floor -rat1 -intrD lt_succ_floor. Qed.

Lemma floorQ_epslt1 (r : rat) : 0 <= r - (Num.floor r)%:Q < 1.
Proof. by rewrite subr_ge0 ltrBlDl floorQ_spec. Qed.

Lemma floorQ_grows (r1 r2 : rat) : r1 <= r2 -> Num.floor r1 <= Num.floor r2.
Proof. exact: floor_le. Qed.

Lemma floorQ_unique (r : rat) (m : int) :
  m%:Q <= r < (m + 1)%:Q -> m = Num.floor r.
Proof. by move=> ?; apply/esym/floor_def. Qed.

Lemma floorQ_int (m : int) : m = Num.floor m%:Q.
Proof. exact/esym/intrKfloor. Qed.

Lemma floorQ_ge0 (r : rat) : 0 <= r -> 0 <= Num.floor r.
Proof. by rewrite -floor_ge_int. Qed.

Lemma floorQ_ge1 (r : rat) : 1 <= r -> 1 <= Num.floor r.
Proof. by rewrite -floor_ge_int. Qed.

Lemma floor_addEpsilon (m : int) (epsilon : rat) :
  0 <= epsilon < 1 -> Num.floor (m%:Q + epsilon) = m.
Proof. by move=> H; apply/floor_def; rewrite lerDl intrD ltrD2l. Qed.

Lemma floorQ_div (q : rat) (m : nat) :
  Num.floor (q / m.+1%:Q) = Num.floor ((Num.floor q)%:Q / m.+1%:Q).
Proof.
apply/floorQ_unique; move: (floorQ_spec q) (floorQ_spec (q / m.+1%:Q)).
rewrite !ler_pdivlMr ?ltr_pdivrMr ?ltr0z // intrD -intrM ler_int.
move=> /andP[_ Hq] /andP[Hdiv /le_lt_trans ->] //.
by rewrite -ltzD1 -(ltr_int rat) intrD (le_lt_trans Hdiv).
Qed.

(* Lemma floorQ_div_pos (q : rat) (m : nat) : *)
(*   (m > 0)%N -> *)
(*   Num.floor (q / m%:Q) = Num.floor ((Num.floor q)%:Q / m%:Q). *)
(* Proof. *)

(* Lemma foo (n m : int) : m%:Q / n%:Q = m%:Q + n%:Q. *)
(* case: (divqP m n).   *)

Lemma floorQ_divn (m : nat) (n : nat) :
  Num.floor (m%:Q / n.+1%:Q) = Num.floor (m %/ n.+1)%N%:Q.
Proof.
apply/esym/floorQ_unique.
rewrite -floorQ_int ler_pdivlMr ?ltr_pdivrMr ?ltr0z //.
rewrite -!natrM ler_nat ltr_nat mulnDl mul1n.
by rewrite [m in (_ <= m < _)%N](divn_eq m n.+1) leq_addr ltn_add2l ltn_mod.
Qed.

(* Lemma floorQ_divn_pos (m n : nat) : *)
(*   (n > 0)%N -> Num.floor (m%:Q / n%:Q) = Num.floor (m %/ n)%N%:Q. *)
(* Proof. *)
(* by case: n => [|n] // H ; apply: floorQ_divn. *)
(* Qed. *)

Lemma helper1 n1 n2 n3 :
  (n2 > 0)%N -> (n3 > 0)%N ->
  ((n1 %/ n2) %/ n3)%N = Num.floor (n1%:Q / (n2 * n3)%N%:Q) :> int.
Proof.
case: n2 =>[|n2] //; case: n3 => [|n3] // => Hpos2 Hpos3.
by rewrite -divnMA mulSn addSn floorQ_divn -floorQ_int.
Qed.

(* Lemma helper2 (n1 n2 n3 : nat) : *)
(*   (n2 > 0)%N -> (n3 > 0)%N -> *)
(*   Num.floor ((n1 %/ n2) %/ n3)%N%:Q = Num.floor ((n1 %/ n3) %/ n2)%N%:Q :> int. *)
(* Proof. *)
(* move => Hn2 Hn3. *)
(* by rewrite helper1 // mulnC -helper1 //. *)
(* Qed. *)
