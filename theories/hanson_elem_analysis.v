From mathcomp Require Import all_ssreflect all_algebra all_field.

Require Import floor posnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import extra_mathcomp.

Require Import hanson_elem_arith.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Notation "r '%:C'" := (ratr r : algC) (at level 8). (* random level *)

(* Section presenting the theory of exp_quo, which corresponds to
taking a rational exponent of a complex algebraic number *)
Section RationalPower.

Definition exp_quo r p q := (q.-root r%:C) ^+ p.

Arguments exp_quo r p%nat q%nat : simpl never.

Lemma exp_quo_0 p q : exp_quo 0 p q = (p == 0%N)%:R.
Proof. by rewrite /exp_quo /ratr mul0r rootC0 expr0n. Qed.

Lemma exp_quo_1 p q : (0 < q)%N -> exp_quo 1 p q = 1.
Proof. by move => Hq; rewrite /exp_quo rmorph1 rootC1 // expr1n. Qed.

Lemma exp_quo_less r1 r2 p q :
  (0 < q)%N -> 0 <= r1 -> 0 <= r2 -> r1 <= r2 ->
  exp_quo r1 p q <= exp_quo r2 p q.
Proof.
move => Hq H1 H2 Hleq; apply: ler_expn2r.
- by rewrite nnegrE rootC_ge0 // ler0q.
- by rewrite nnegrE rootC_ge0 // ler0q.
- by rewrite ler_rootCl ?ler_rat // nnegrE ler0q.
Qed.

Lemma exp_quo_lessn r1 (p1 q1 p2 q2 : nat) :
  (0 < q1)%N -> (0 < q2)%N -> 1 <= r1 -> (p1 * q2 <= p2 * q1)%N ->
  exp_quo r1 p1 q1 <= exp_quo r1 p2 q2.
Proof.
move => Hq1 Hq2 H1r Hle.
have H0r : 0 <= r1 by apply/le_trans/H1r/ler01.
have Hprodpos : (0 < q1 * q2)%N by rewrite muln_gt0 Hq1 Hq2.
suff : (q1.-root r1%:C ^+ p1) ^+ (q1 * q2) <=
       (q2.-root r1%:C ^+ p2) ^+ (q1 * q2).
  by rewrite ler_pexpn2r // nnegrE; apply: exprn_ge0; rewrite rootC_ge0 ?ler0q.
rewrite !exprM [_ ^+ _ ^+ q1]exprAC -exprM ![_ ^+ _ ^+ q2]exprAC !rootCK //.
by rewrite -exprM; apply: ler_weexpn2l; rewrite // ler1q.
Qed.

Lemma exp_quo_r_nat r i : (r ^+ i)%:C = exp_quo r i 1.
Proof. by rewrite /exp_quo root1C CratrE /=. Qed.

Lemma exp_quo_nat_nat i j : (i ^ j)%:R%:C = exp_quo i%:Q j 1.
Proof. by rewrite natrX exp_quo_r_nat. Qed.

Lemma exp_quo_mult_distr r1 r2 p1 q1 (Hr2 : 0 <= r2) :
  exp_quo r1 p1 q1 * exp_quo r2 p1 q1 = exp_quo (r1 * r2) p1 q1.
Proof. by rewrite /exp_quo rmorphM /= [in RHS]rootCMr ?exprMn ?ler0q. Qed.

Lemma exp_quo_plus r1 p1 q1 p2 q2 :
  (0 < q1)%N -> (0 < q2)%N -> 0 <= r1 ->
  exp_quo r1 (p1 * q2 + p2 * q1) (q1 * q2) =
  exp_quo r1 p1 q1 * exp_quo r1 p2 q2.
Proof.
move => Hq1pos Hq2pos Hr1pos.
have Hprodpos : (0 < q1 * q2)%N.
  by rewrite muln_gt0 Hq1pos Hq2pos.
rewrite /exp_quo.
set t1 := LHS.
set t2 := RHS.
suff: t1 ^+ (q1 * q2) = t2 ^+ (q1 * q2).
  apply: pexpIrn; rewrite // nnegrE /t1 /t2.
  + by apply: exprn_ge0; rewrite rootC_ge0 ?ler0q.
  + by apply: mulr_ge0; apply: exprn_ge0; rewrite rootC_ge0 ?ler0q.
rewrite /t1 /t2 -exprM mulnDl exprD prod_root ?ler0q // exprMn !exprM.
rewrite ![_ ^+ _ ^+ q1]exprAC [_ ^+ p1 ^+ q2]exprAC !rootCK // -exprM.
rewrite [_ ^+ p2 ^+ q1]exprAC 2![_ ^+ _ ^+ q2]exprAC !rootCK // -exprM.
rewrite ![_ ^+ _ ^+ q1]exprAC rootCK // -exprM.
by rewrite ![_ ^+ _ ^+ q2]exprAC rootCK // -exprM [(p2 * _)%N]mulnC.
Qed.

Lemma exp_quo_equiv r1 p1 q1 p2 q2 :
  (0 < q1)%N -> (0 < q2)%N -> 0 <= r1 -> (p1 * q2 = p2 * q1)%N ->
  exp_quo r1 p1 q1 = exp_quo r1 p2 q2.
Proof.
move => Hq1pos Hq2pos Hr1pos Heq.
have Hprodpos : (0 < q1 * q2)%N by rewrite muln_gt0 Hq1pos Hq2pos.
suff : q1.-root r1%:C ^+ p1 ^+ (q1 * q2) = q2.-root r1%:C ^+ p2 ^+ (q1 * q2).
  by apply: pexpIrn; rewrite // nnegrE exprn_ge0 ?rootC_ge0 ?ler0q.
rewrite !exprM ![_ ^+ _ ^+ q1]exprAC -exprM ![_ ^+ _ ^+ q2]exprAC !rootCK //.
by rewrite -exprM Heq mulnC.
Qed.

Lemma exp_quo_ge0 r p q : (0 < q)%N -> 0 <= r -> 0 <= exp_quo r p q.
Proof. by move=> Hq Hr; rewrite exprn_gte0 ?rootC_ge0 ?ler0q. Qed.

Lemma exp_quo_gt0 r p q : (0 < q)%N -> (0 < r) ->  0 < exp_quo r p q.
Proof. by move => Hq Hr; rewrite exprn_gte0 ?rootC_gt0 ?ltr0q. Qed.

Lemma exp_quo_ge1 r p q : (0 < q)%N -> (1 <= r) -> 1 <= exp_quo r p q.
Proof. by move => Hq Hr; rewrite exprn_ege1 ?rootC_ge1 ?ler1q. Qed.

Lemma exp_quo_gt1 r p q : (0 < p)%N -> (0 < q)%N -> 1 < r -> 1 < exp_quo r p q.
Proof. by move => Hp Hq Hr; rewrite exprn_egt1 ?rootC_gt1 ?ltr1q -?lt0n. Qed.

Lemma sqrtC_exp_quo (r : rat) : sqrtC r%:C = exp_quo r 1%N 2%N.
Proof. by rewrite /exp_quo expr1. Qed.

Lemma exp_quo_self_grows (p1 q1 p2 q2 : nat) r1 r2 :
  (0 < q1)%N ->
  (0 < q2)%N ->
  r1 = p1%:Q / q1%:Q ->
  r2 = p2%:Q / q2%:Q ->
  0 < r1 ->
  1 <= r2 ->
  r1 <= r2 ->
  exp_quo r1 p1 q1 <= exp_quo r2 p2 q2.
Proof.
move => Hq1 Hq2 Hr1 Hr2 Hr1gt0 Hle1r2 Hle12.
have Hr1pos : 0 <= r1 by apply: ltW.
have Hr2pos : 0 <= r2 by rewrite Hr2 divr_ge0 // ?ler0z.
have Hprodpos : (0 < q1 * q2)%N by rewrite muln_gt0 Hq1 Hq2.
have Hleq : (p1 * q2 <= p2 * q1)%N.
  rewrite -(ler_nat [numDomainType of rat]) !natrM -ler_pdivl_mulr ?ltr0n //.
  by rewrite mulrAC -ler_pdivr_mulr ?ltr0n //; move: Hle12; rewrite Hr1 Hr2.
have -> : exp_quo r2 p2 q2 =
          exp_quo r2 p1 q1 * exp_quo r2 (p2 * q1 - p1 * q2)%N (q1 * q2)%N.
  rewrite -exp_quo_plus //; apply: exp_quo_equiv => //. (* TODO: lia *)
    by rewrite !muln_gt0 Hq1 Hq2.
  by rewrite [in RHS]mulnA mulnAC -mulnDl subnKC // !mulnA.
have -> : exp_quo r2 p1 q1 = exp_quo r1 p1 q1 * exp_quo (r2 / r1) p1 q1.
  by rewrite exp_quo_mult_distr ?divr_ge0 // mulrC divfK ?lt0r_neq0.
rewrite -mulrA; apply/ler_pemulr/mulr_ege1/exprn_ege1.
- exact: exp_quo_ge0.
- by apply: exprn_ege1; rewrite rootC_ge1 // ler1q ler_pdivl_mulr // mul1r.
- by rewrite rootC_ge1 // ler1q.
Qed.

End RationalPower.

(* This Section contains a collection of four facts used in the proof
of Hanson's lemma: a comparison of factorial to a geometric sequence,
the formula for summing a geometric sequence, and a bound on (1 + 1 /
x) ^ x *)
Section FourFacts.

(* A lemma comparing factorial to a geometric sequence *)
Lemma fact_greater_geom i : i.+1`!%:R >= (3%:Q / 2%:Q) ^+ i.
Proof.
elim: i => // i IHi; rewrite exprS factS natrM; apply: ler_pmul IHi => //.
by rewrite ler_pdivr_mulr ?ltr0n // mulr_natr -mulrnA ler_nat.
Qed.

(* Formula for a geometric sum in a field *)
Lemma geometric_sum (R : numFieldType) n (r : R) (Hr : r != 1) :
  \sum_(i < n) r ^+ i = (1 - r ^+ n) / (1 - r).
Proof.
elim: n => [|n Hn]; first by rewrite big_ord0 expr0 subrr mul0r.
have den_neq0 : 1 - r != 0 by rewrite subr_eq0 eq_sym.
rewrite big_ord_recr /= Hn; apply: canRL (mulfK den_neq0) _.
by rewrite [LHS]mulrDl divfK // mulrBr mulr1 addrA subrK exprSr.
Qed.

(* A bound on (1 + 1 / (n+1)) ^ (n+2) *)
Lemma one_plus_invn_expn (n : nat) : (1 + n%:Q^-1) ^+ n.+1 <= 8%:Q.
Proof.
case: n => // n.
have step: (1 + n.+1%:Q^-1) ^+ n.+1 <= \sum_(i < n.+2) i`!%:Q^-1.
  rewrite exprDn; apply: ler_sum => i _; rewrite expr1n mul1r -mulr_natr exprVn.
  rewrite ler_pdivr_mull ?ler_pdivl_mulr ?ltr0n ?expn_gt0 ?fact_gt0 //.
  by rewrite -natrM bin_ffact -natrX ler_nat ffact_le_expn.
have {step}: (1 + n.+1%:Q^-1) ^+ n.+2 <= 2%:Q * \sum_(i < n.+2) i`!%:Q^-1.
  rewrite exprS; apply: ler_pmul => //.
  by rewrite -[2%:Q]/(1 + 1) ler_add2l invf_le1 // ler1z.
move/le_trans; apply; rewrite -[8%:Q]/(2%:Q * 4%:Q) ler_pmul2l //.
have: 1 + \sum_(i < n.+1) (2%:Q / 3%:Q) ^+ i <= 4%:Q.
  rewrite geometric_sum // -[4%:Q]/(1 + 3%:Q) ler_add2l.
  have -> : 1 - 2%:Q / 3%:Q = 3%:Q^-1 by [].
  by rewrite invrK ler_pimull // ler_subl_addr ler_addl.
apply: le_trans; rewrite big_ord_recl ler_add2l; apply: ler_sum => i _ /=.
by rewrite -invf_div exprVn lef_pinv ?posrE ?ltr0n ?fact_gt0 ?fact_greater_geom.
Qed.

(* TODO : clean up, use more ^-1 *)
(* this proof is very long in big part because of exp_quo *)
Lemma one_plus_invx_expx (p q : nat) (r : rat) (n : nat) :
  0 < r -> r = p%:Q / q%:Q -> exp_quo (1 + 1 / r) p q <= ratr 9%:Q.
Proof.
rewrite div1r => Hrpos Hrpq.

have Hp : (0 < p)%N.
  by apply/contraTT: Hrpos; rewrite Hrpq -eqn0Ngt => /eqP ->; rewrite mul0r.
have Hq : (0 < q)%N.
  apply/contraTT: Hrpos; rewrite Hrpq -eqn0Ngt => /eqP ->.
  by rewrite invr0 mulr0.
have [H1r|Hr1] := leP 1 r.

(* First part : 1 <= r *)
have := floorQ_spec r.
set f := floorQ r => /andP[Hf1 Hf2].
have/ZnatP[m Hfm] : f \is a Znat by rewrite Znat_def; apply/floorQ_ge0/ltW.

apply: (@le_trans _ _ (ratr 8%:Q)); last by rewrite ler_rat.
have Hle1m : (1 <= m)%N by have := floorQ_ge1 H1r; rewrite -/f Hfm.

have Hfloor_inv : (f + 1)%:Q^-1 < r^-1 <= f%:Q^-1.
  rewrite lef_pinv ?ltf_pinv //= ?posrE ?ltr0z.
  - by rewrite andbC mulrzDl floorQ_spec.
  - by rewrite gtz0_ge1 ler_addr floorQ_ge0 // ltW.
  - by rewrite gtz0_ge1 floorQ_ge1.

(* a few helpers which will be needed in the intermediate steps *)
have Helper1 : 0 <= r by exact: ltW.
have Helper2 : 0 <= r^-1 by rewrite invr_ge0.
have Helper3 : 0 <= 1 + r^-1 by exact: addr_ge0.
have Helper4 : 0 <= f%:Q^-1 by rewrite invr_ge0 Hfm ler0n.
have Helper5 : 0 <= 1 + f%:Q^-1 by rewrite addr_ge0.
have Helper6 : 1 <= 1 + f%:Q^-1 by rewrite ler_addl.

suff Hinterm : exp_quo (1 + r^-1) p q <= exp_quo (1 + f%:Q^-1) m.+1 1.
  apply: (le_trans Hinterm).
  by rewrite Hfm -exp_quo_r_nat ler_rat one_plus_invn_expn.
apply/le_trans.
  apply: (@exp_quo_less _ (1 + f%:Q^-1)) => //.
  by rewrite ler_add2l; case/andP: Hfloor_inv.
apply: exp_quo_lessn => //.
move: Hf2.
rewrite muln1 Hfm -rat1 -natrD addn1 Hrpq ltr_pdivr_mulr ?ltr0z //.
by rewrite -natrM ltr_nat; exact: leqW.

(* r <= 1 *)
have := floorQ_spec r^-1.
set f := floorQ r^-1 => /andP[Hf1 Hf2].
have Hfnat : f \is a Znat by rewrite Znat_def floorQ_ge0 // invr_ge0 ltW.
move/ZnatP: Hfnat => [] m Hfm.

have Helper0 : 0 < f%:Q.
  by rewrite ltr0z gtz0_ge1 floorQ_ge1 // invf_ge1 // ltW.
have Helper1 : (0 < m)%N.
  by move: Helper0; rewrite Hfm ltr0n.
have Helper2 : 0 < f%:Q + 1.
  by rewrite ltr_paddr.
have Helper3 : r <= f%:Q^-1.
  by rewrite -lef_pinv ?posrE ?invr_gt0 // invrK.
have Helper4 : 0 <= 1 + r^-1.
  by rewrite ler_paddl //; apply/le_trans/Hf1/ltW.
have Helper5 : 0 <= 1 + (1 + f%:Q).
  by rewrite Hfm -rat1 -!intrD ler0n.
have Helper6 : 1 + r^-1 <= 1 + (1 + f%:Q).
  by rewrite ler_add2l addrC; apply: ltW.
have Helper7 : 1 <= 1 + (1 + f%:Q).
  by rewrite Hfm -rat1 -!intrD ler1n.
have Helper8 : (p * m <= q)%N.
  move: Hf1; rewrite Hfm Hrpq invfM invrK.
  by rewrite ler_pdivl_mull ?ltr0z // -intrM ler_int.

have Hfloor_inv : (f%:Q + 1)^-1 < r <= f%:Q^-1.
  by rewrite -[r]invrK lef_pinv ?ltf_pinv ?Hf1 ?Hf2 // posrE invr_gt0.
apply: (@le_trans _ _ (exp_quo (1 + (1 + f%:Q)) p q)).
  exact: exp_quo_less.
apply: (@le_trans _ _ (exp_quo (1 + (1 + f%:Q)) 1 m)).
  by apply: exp_quo_lessn=> //; rewrite mul1n.
apply: (@le_trans _ _ (exp_quo (((3 ^ (m.+1))%N)%:Q) 1 m)).
  apply: exp_quo_less => //; first exact: ler0n.
  by rewrite -rat1 Hfm -!natrD ler_nat !add1n replace_exponential.
rewrite /exp_quo expr1 !CratrE /= expnS natrM rootCMr ?ler0n //.
have -> : 9%:R = 3%:R * 3%:R :> algC by rewrite -natrM.
rewrite ler_pmul ?rootC_ge0 ?ler0n //.
  case: m Hfm Helper1 Helper8 => [|m]// _ _ _; exact: le_mrootn_n.
  (* TODO: make a lemma out of this *)
by rewrite natrX exprCK // ?CratrE // ler0n.
Qed.

End FourFacts.
