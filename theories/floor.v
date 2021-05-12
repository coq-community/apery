From mathcomp Require Import all_ssreflect all_algebra.

Require Import field_tactics.
Require Import bigopz.
Require Import lia_tactics conj.
Require Import shift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope ring_scope.

(* reminder: Posz k = k, Negz k = (-(k+1)) *)
Definition floorQ (r : rat) := (numq r %/ denq r)%Z.

Lemma floorQ_spec (r : rat) : ((floorQ r)%:Q <= r < (floorQ r)%:Q + 1)%Q.
Proof.
set p := numq r.
set q := denq r.
have Hfloor_r : floorQ r = (p %/ q)%Z by [].
have Hrpq : r = p%:Q / q%:Q by rewrite -[r]divq_num_den.
have EqEuclid : p = (p %/ q)%Z * q + (p %% q)%Z by apply: divz_eq.
have qnot0 : q%:Q != 0 by rewrite intq_eq0; apply: denq_neq0.
have qgt0 : 0 < q by exact: denq_gt0.
have qrge0 :  0 <= q%:~R :> rat by rewrite ler0z ?ltW.
have EqEuclidQ : r = (p %/ q)%Z%:Q + ((p %% q)%Z%:Q / q%:Q) .
  apply: (mulIf qnot0); set rq := q%:~R.
  by rewrite mulrDl Hrpq  !(mulfVK qnot0) /rq -rmorphM /= -rmorphD /= -EqEuclid.
rewrite Hfloor_r EqEuclidQ.
apply/andP; split.
  - by rewrite cpr_add divr_ge0 // ler0z; apply: modz_ge0; exact: denq_neq0.
  - by rewrite ltr_add2l ltr_pdivr_mulr ?ltr0z // mul1r ltr_int ltz_pmod.
Qed.


Lemma floorQ_epslt1 (r : rat) : 0 <= (r - (floorQ r)%:Q)%Q < 1.
Proof.
apply/andP.
have := (floorQ_spec r).
case/andP.
split.
  by rewrite lter_sub_addr add0r.
by rewrite lter_sub_addr addrC.
Qed.

Lemma floorQ_grows (r1 r2 : rat) : (r1 <= r2) -> floorQ r1 <= floorQ r2.
Proof.
move => Hr12.
rewrite -ltz_addr1.
suff: (floorQ r1)%:Q < (floorQ r2 + 1)%:Q by rewrite ltr_int.
have Hle12 : (floorQ r1)%:Q <= r2.
  have Hle1 : (floorQ r1)%:Q <= r1 by case/andP: (floorQ_spec r1).
  by apply: (le_trans Hle1).
apply: (le_lt_trans Hle12).
by rewrite intrD; case/andP: (floorQ_spec r2).
Qed.

Lemma floorQ_unique (r : rat) (m : int) : m%:Q <= r < (m + 1)%:Q -> m = floorQ r.
Proof.
have HfloorQ := (floorQ_spec r).
move => H.
apply/eqP; rewrite eq_le; apply/andP; split.
- suff: m%:Q < ((floorQ r) + 1)%:Q by rewrite ltr_int ltz_addr1.
  have Hlemr :  m%:Q <= r by case/andP: H.
  apply: (le_lt_trans Hlemr); by case/andP: HfloorQ; rewrite intrD.
- rewrite -ltz_addr1.
  have Hleflm : (floorQ r)%:Q <= r by case/andP: HfloorQ.
  suff: (floorQ r)%:Q < (m + 1)%:Q by rewrite ltr_int.
  apply: (le_lt_trans Hleflm).
  by case/andP: H.
Qed.

Lemma floorQ_int (m : int) : m = floorQ m%:Q.
Proof.
apply: floorQ_unique; apply/andP; split => // .
by rewrite ltr_int ltz_addr1.
Qed.

Lemma floorQ_ge0 (r : rat) : (0 <= r) -> 0 <= floorQ r.
Proof.
move => Hrge0.
have -> : 0 = floorQ (0%:Z%:Q).
  by rewrite -floorQ_int.
exact: floorQ_grows.
Qed.

Lemma floorQ_ge1 (r : rat) : (1 <= r) -> 1 <= floorQ r.
Proof.
move => Hrge0.
have -> : 1 = floorQ (1%:Z%:Q).
  by rewrite -floorQ_int.
exact: floorQ_grows.
Qed.

Lemma floor_addEpsilon (m : int) (epsilon : rat) : (0 <= epsilon < 1) -> floorQ (m%:Q + epsilon) = m.
Proof.
move => Heps; symmetry.
apply: floorQ_unique.
apply/andP; split.
rewrite ler_addl.
by case/andP: Heps.
rewrite intrD.
rewrite ltr_add2l.
by case/andP: Heps.
Qed.

Lemma floorQ_div (q : rat) (m : nat) : floorQ (q / m.+1%:Q) = floorQ ((floorQ q)%:Q / m.+1%:Q).
have usedAlot : m.+1%:Q != 0 by rewrite intq_eq0.
have usedALot1 : 0 < m.+1%:Q by rewrite -rat0 ltr_int // .
have usedALot2 : 0 <= m.+1%:Q by rewrite -rat0 ler_int // .
have Hq1 : q = (floorQ q)%:Q + (q - (floorQ q)%:Q).
  rewrite addrC -addrA.
  by rewrite  [(-_ + _)]addrC subrr addr0.
have floorEuclid := (divz_eq (floorQ q) m.+1).
rewrite {1}floorEuclid in Hq1.
have Heps : (floorQ q %% m.+1)%Z%:Q +
        (q - (floorQ q)%:~R) < m.+1%:Q.
rewrite -addn1 PoszD intrD .
apply: ler_lt_add.
rewrite ler_int -ltz_addr1.
apply: ltz_pmod.
rewrite -PoszD addn1 ltz_nat // .
by case/andP: (floorQ_epslt1 q).
suff Hdecomp : q / m.+1%:~R = ((floorQ q %/ m.+1)%Z%:Q + (((floorQ q %% m.+1)%Z)%:~R + (q - (floorQ q)%:~R)) / m.+1%:Q).
rewrite Hdecomp.
suff HdivQdivz : floorQ ((floorQ q)%:~R / m.+1%:~R) = floorQ (((floorQ q) %/ m.+1)%Z%:Q).
set epsilon := ((floorQ q %% m.+1)%Z%:~R + (q - (floorQ q)%:~R)) / m.+1%:~R.
rewrite HdivQdivz -floorQ_int.
apply: floor_addEpsilon.
  rewrite /epsilon.
  apply/andP; split.
  - apply: divr_ge0.
    apply: addr_ge0.
    rewrite -rat0 ler_int; apply: modz_ge0 => // .
    by case/andP: (floorQ_epslt1 q).
    by rewrite -rat0 ler_int // .
  - rewrite ltr_pdivr_mulr ?mul1r.
    exact: Heps.
    by rewrite -rat0 ltr_int // .
rewrite {1}floorEuclid.
rewrite intrD mulrDl.
set eps2 := (floorQ q %% m.+1)%Z%:~R / m.+1%:~R.
have -> : ((floorQ q %/ m.+1)%Z * m.+1)%:~R / m.+1%:~R = ((floorQ q %/ m.+1)%Z)%:Q by rewrite intrM mulfK.
rewrite (@floor_addEpsilon _ eps2).
  - by rewrite -floorQ_int.
  - apply/andP; split.
    + apply: divr_ge0 => // .
      rewrite -rat0 ler_int; apply: modz_ge0 => // .
    + rewrite ltr_pdivr_mulr ?mul1r // .
      rewrite ltr_int. apply: ltz_pmod => // .
rewrite {1}Hq1 intrD.
rewrite -[_ + _ + (_ - _) ]addrA. rewrite [LHS]mulrDl.
congr (_ + _).
rewrite intrM mulfK.
by [].
by rewrite intq_eq0.
Qed.

(* Lemma floorQ_div_pos (q : rat) (m : nat) :  *)
(*   (m > 0)%N -> *)
(*   floorQ (q / m%:Q) = floorQ ((floorQ q)%:Q / m%:Q). *)
(* Proof. *)


(* Lemma foo (n m : int) : m%:Q / n%:Q = m%:Q + n%:Q. *)
(* case: (divqP m n).   *)




Lemma floorQ_divn (m : nat) (n : nat) :
   floorQ (m%:Q / n.+1%:Q) = floorQ (m %/ n.+1)%N%:~R.
Proof.
  rewrite -divz_nat; move: (le0z_nat n.+1).
  case: (divqP m (n.+1)%:Z) => // k x kn0 ple0.
  have {ple0 kn0} lt0k: 0 < k.
    by rewrite lt0r kn0 /= -(pmulr_lge0 _ (denq_gt0 x)).
  by rewrite divzMpl // [LHS]floorQ_int.
Qed.

(* Lemma floorQ_divn_pos (m n : nat) : (n > 0)%N -> floorQ (m%:Q / n%:Q) = floorQ (m %/ n)%N%:~R. *)
(* Proof. *)
(* by case: n => [|n] // H ; apply: floorQ_divn. *)
(* Qed. *)

Lemma helper1 n1 n2 n3 :
  (n2 > 0)%N -> (n3 > 0)%N ->
  ((n1 %/ n2) %/ n3)%N = floorQ (n1%:Q / (n2 * n3)%N%:Q) :> int.
Proof.
case: n2 =>[|n2] //; case: n3 => [|n3] // => Hpos2 Hpos3.
rewrite [LHS]floorQ_int.
rewrite -floorQ_divn // .
rewrite floorQ_div.
rewrite -floorQ_divn.
rewrite -floorQ_div.
rewrite PoszM intrM.
suff -> : n1%:Q / n2.+1%:Q / n3.+1%:Q = n1%:Q / (n2.+1%:Q * n3.+1%:Q) => // .
by rewrite -mulrA -invfM.
Qed.

(* Lemma helper2 n1 n2 n3 : *)
(*   (n2 > 0)%N -> (n3 > 0)%N -> *)
(*   floorQ ((n1 %/ n2) %/ n3)%N%:Q = floorQ ((n1 %/ n3) %/ (n2)%N)%:Q :> int. *)
(* Proof. *)
(* move => Hn2 Hn3. *)
(* by rewrite helper1 // mulnC -helper1 //. *)
(* Qed. *)
