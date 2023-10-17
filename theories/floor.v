From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* reminder: Posz k = k, Negz k = (-(k+1)) *)
Definition floorQ (r : rat) := (numq r %/ denq r)%Z.

Lemma floorQ_spec (r : rat) : (floorQ r)%:Q <= r < (floorQ r)%:Q + 1.
Proof.
rewrite -[r in _ <= r < _]divq_num_den ler_pdivlMr ?ltr_pdivrMr ?ltr0z //.
by rewrite -rat1 -intrD -!intrM ler_int ltr_int lez_floor ?ltz_ceil.
Qed.

Lemma floorQ_epslt1 (r : rat) : 0 <= r - (floorQ r)%:Q < 1.
Proof. by rewrite subr_ge0 ltrBlDl floorQ_spec. Qed.

Lemma floorQ_grows (r1 r2 : rat) : r1 <= r2 -> floorQ r1 <= floorQ r2.
Proof.
move => Hr12.
suff: (floorQ r1)%:Q < (floorQ r2 + 1)%:Q by rewrite ltr_int ltzD1.
rewrite intrD; case/andP: (floorQ_spec r2) => _; apply: le_lt_trans.
by apply: le_trans Hr12; case/andP: (floorQ_spec r1).
Qed.

Lemma floorQ_unique (r : rat) (m : int) : m%:Q <= r < (m + 1)%:Q -> m = floorQ r.
Proof.
have /andP[Hfloor1 Hfloor2] := floorQ_spec r.
case/andP => Hm1 Hm2.
move: (le_lt_trans Hm1 Hfloor2) (le_lt_trans Hfloor1 Hm2).
rewrite -[n in _ + n]rat1 -intrD !ltr_int !ltzD1 => ? ?.
by apply/eqP; rewrite eq_le; apply/andP.
Qed.

Lemma floorQ_int (m : int) : m = floorQ m%:Q.
Proof. by apply: floorQ_unique; rewrite ltr_int ltzD1 !lexx. Qed.

Lemma floorQ_ge0 (r : rat) : 0 <= r -> 0 <= floorQ r.
Proof. by move=> Hrge0; rewrite [0]floorQ_int floorQ_grows. Qed.

Lemma floorQ_ge1 (r : rat) : 1 <= r -> 1 <= floorQ r.
Proof. by move=> Hrge0; rewrite [1]floorQ_int floorQ_grows. Qed.

Lemma floor_addEpsilon (m : int) (epsilon : rat) :
  0 <= epsilon < 1 -> floorQ (m%:Q + epsilon) = m.
Proof.
move=> /andP[Heps1 Heps2].
by apply/esym/floorQ_unique; rewrite lerDl Heps1 intrD ltrD2l.
Qed.

Lemma floorQ_div (q : rat) (m : nat) :
  floorQ (q / m.+1%:Q) = floorQ ((floorQ q)%:Q / m.+1%:Q).
Proof.
apply/floorQ_unique; move: (floorQ_spec q) (floorQ_spec (q / m.+1%:Q)).
rewrite !ler_pdivlMr ?ltr_pdivrMr ?ltr0z // intrD -intrM ler_int.
move=> /andP[_ Hq] /andP[Hdiv /le_lt_trans ->] //.
by rewrite -ltzD1 -(ltr_int rat) intrD (le_lt_trans Hdiv).
Qed.

(* Lemma floorQ_div_pos (q : rat) (m : nat) :  *)
(*   (m > 0)%N -> *)
(*   floorQ (q / m%:Q) = floorQ ((floorQ q)%:Q / m%:Q). *)
(* Proof. *)

(* Lemma foo (n m : int) : m%:Q / n%:Q = m%:Q + n%:Q. *)
(* case: (divqP m n).   *)

Lemma floorQ_divn (m : nat) (n : nat) :
  floorQ (m%:Q / n.+1%:Q) = floorQ (m %/ n.+1)%N%:Q.
Proof.
apply/esym/floorQ_unique.
rewrite -floorQ_int ler_pdivlMr ?ltr_pdivrMr ?ltr0z //.
rewrite -!natrM ler_nat ltr_nat mulnDl mul1n.
by rewrite [m in (_ <= m < _)%N](divn_eq m n.+1) leq_addr ltn_add2l ltn_mod.
Qed.

(* Lemma floorQ_divn_pos (m n : nat) : (n > 0)%N -> floorQ (m%:Q / n%:Q) = floorQ (m %/ n)%N%:Q. *)
(* Proof. *)
(* by case: n => [|n] // H ; apply: floorQ_divn. *)
(* Qed. *)

Lemma helper1 n1 n2 n3 :
  (n2 > 0)%N -> (n3 > 0)%N ->
  ((n1 %/ n2) %/ n3)%N = floorQ (n1%:Q / (n2 * n3)%N%:Q) :> int.
Proof.
case: n2 =>[|n2] //; case: n3 => [|n3] // => Hpos2 Hpos3.
by rewrite -divnMA mulSn addSn floorQ_divn -floorQ_int.
Qed.

(* Lemma helper2 n1 n2 n3 : *)
(*   (n2 > 0)%N -> (n3 > 0)%N -> *)
(*   floorQ ((n1 %/ n2) %/ n3)%N%:Q = floorQ ((n1 %/ n3) %/ (n2)%N)%:Q :> int. *)
(* Proof. *)
(* move => Hn2 Hn3. *)
(* by rewrite helper1 // mulnC -helper1 //. *)
(* Qed. *)
