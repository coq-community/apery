From mathcomp Require Import all_ssreflect all_algebra all_field.
Require Import extra_mathcomp posnum hanson_elem_arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Notation "r '%:C'" := (ratr r : algC) (at level 8). (* random level *)

(* Section presenting the theory of exp_quo, which corresponds to
taking a rational exponent of a complex algebraic number *)
Section RationalPower.

Definition exp_quo r p q := q.-root r%:C ^+ p.

Arguments exp_quo r p%nat q%nat : simpl never.

Lemma exp_quo_0 p q : exp_quo 0 p q = (p == 0%N)%:R.
Proof. by rewrite /exp_quo /ratr mul0r rootC0 expr0n. Qed.

Lemma exp_quo_1 p q : (0 < q)%N -> exp_quo 1 p q = 1.
Proof. by move => Hq; rewrite /exp_quo rmorph1 rootC1 // expr1n. Qed.

Lemma exp_quoMl r1 r2 p1 q1 (Hr1 : 0 <= r1) :
  exp_quo (r1 * r2) p1 q1 = exp_quo r1 p1 q1 * exp_quo r2 p1 q1.
Proof. by rewrite /exp_quo rmorphM /= rootCMl ?exprMn ?ler0q. Qed.

Lemma exp_quoMr r1 r2 p1 q1 (Hr2 : 0 <= r2) :
  exp_quo (r1 * r2) p1 q1 = exp_quo r1 p1 q1 * exp_quo r2 p1 q1.
Proof. by rewrite mulrC exp_quoMl // mulrC. Qed.

Lemma exp_quoV r p q : 0 <= r -> exp_quo r^-1 p q = (exp_quo r p q)^-1.
Proof.
rewrite /exp_quo fmorphV /=; case: q => [|q] r_ge_0.
  by rewrite !root0C expr0n; case: eqP; rewrite (invr0, invr1).
by rewrite rootCV ?ler0q // exprVn.
Qed.

Lemma exp_quo_lessE r1 r2 p1 q1 p2 q2 :
    0 <= r1 -> 0 <= r2 -> (0 < q1)%N -> (0 < q2)%N ->
    (exp_quo r1 p1 q1 <= exp_quo r2 p2 q2) =
    (r1%:C ^+ (p1 * q2) <= r2%:C ^+ (p2 * q1)).
Proof.
move=> Hr1 Hr2 Hq1 Hq2; rewrite /exp_quo -!rootCX ?ler0q //.
rewrite root_le_x // ?rootC_ge0 ?exprn_ge0 ?ler0q //.
by rewrite -rootCX ?root_x_le ?exprn_ge0 ?ler0q // -!exprM.
Qed.

Lemma exp_quo_less r1 r2 p q :
  (0 < q)%N -> 0 <= r1 -> 0 <= r2 -> r1 <= r2 ->
  exp_quo r1 p q <= exp_quo r2 p q.
Proof.
move => Hq H1 H2 Hleq.
by rewrite exp_quo_lessE // lerXn2r ?ler_rat // nnegrE ler0q.
Qed.

Lemma exp_quo_lessn r1 (p1 q1 p2 q2 : nat) :
  (0 < q1)%N -> (0 < q2)%N -> 1 <= r1 -> (p1 * q2 <= p2 * q1)%N ->
  exp_quo r1 p1 q1 <= exp_quo r1 p2 q2.
Proof.
move => Hq1 Hq2 H1r Hle.
have H0r : 0 <= r1 by apply/le_trans/H1r/ler01.
by rewrite exp_quo_lessE // exp_incr_expp ?ler1q.
Qed.

Lemma exp_quo_r_nat r i : (r ^+ i)%:C = exp_quo r i 1.
Proof. by rewrite /exp_quo root1C CratrE /=. Qed.

Lemma exp_quo_nat_nat i j : (i ^ j)%:R%:C = exp_quo i%:Q j 1.
Proof. by rewrite natrX exp_quo_r_nat. Qed.

Lemma exp_quo_plus r1 p1 q1 p2 q2 :
  (0 < q1)%N -> (0 < q2)%N -> 0 <= r1 ->
  exp_quo r1 (p1 * q2 + p2 * q1) (q1 * q2) =
  exp_quo r1 p1 q1 * exp_quo r1 p2 q2.
Proof.
move => Hq1pos Hq2pos Hr1pos.
rewrite [LHS]exprD [in l in l * _ = _]mulnC !prod_root ?ler0q //.
by rewrite mulnC exprM mulnC exprM !rootCK.
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
have: r1%:C ^+ (p1 * q2) <= r2%:C ^+ (p1 * q2).
  by rewrite lerXn2r ?ler_rat // nnegrE ler0q.
rewrite exp_quo_lessE // => /le_trans -> //; rewrite exp_incr_expp ?ler1q //.
move: Hle12; rewrite Hr1 Hr2 ler_pdivrMr ?ltr0n //.
by rewrite mulrAC ler_pdivlMr ?ltr0n // -!natrM ler_nat.
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
elim: i => // i IHi; rewrite exprS factS natrM; apply: ler_pM IHi => //.
by rewrite ler_pdivrMr ?ltr0n // mulr_natr -mulrnA ler_nat.
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
  rewrite ler_pdivrMl ?ler_pdivlMr ?ltr0n ?expn_gt0 ?fact_gt0 //.
  by rewrite -natrM bin_ffact -natrX ler_nat ffact_le_expn.
have {step}: (1 + n.+1%:Q^-1) ^+ n.+2 <= 2%:Q * \sum_(i < n.+2) i`!%:Q^-1.
  rewrite exprS; apply: ler_pM => //.
  by rewrite -[2%:Q]/(1 + 1) lerD2l invf_le1 // ler1z.
move/le_trans; apply; rewrite -[8%:Q]/(2%:Q * 4%:Q) ler_pM2l //.
have: 1 + \sum_(i < n.+1) (2%:Q / 3%:Q) ^+ i <= 4%:Q.
  rewrite geometric_sum // -[4%:Q]/(1 + 3%:Q) lerD2l.
  have -> : 1 - 2%:Q / 3%:Q = 3%:Q^-1 by [].
  by rewrite invrK ler_piMl // lerBlDr lerDl.
apply: le_trans; rewrite big_ord_recl lerD2l; apply: ler_sum => i _ /=.
by rewrite -invf_div exprVn lef_pV2 ?posrE ?ltr0n ?fact_gt0 ?fact_greater_geom.
Qed.

(* TODO : clean up, use more ^-1 *)
(* this proof is very long in big part because of exp_quo *)
Lemma one_plus_invx_expx (p q : nat) :
  0 < p%:Q / q%:Q -> exp_quo (1 + q%:Q / p%:Q) p q <= ratr 9%:Q.
Proof.
move=> /ltr_neq.
rewrite eq_sym mulf_eq0 invr_eq0 negb_or !intr_eq0 -!lt0n => /andP[Hp Hq].
have [leqp|ltpq] := leqP q p.

(* First part : q <= p *)
pose f := (p %/ q)%N.
apply: (@le_trans _ _ (ratr 8%:Q)); last by rewrite ler_rat.
suff: exp_quo (1 + q%:~R / p%:~R) p q <= exp_quo (1 + f%:Q^-1) f.+1 1.
  by move=> /le_trans -> //; rewrite -exp_quo_r_nat ler_rat one_plus_invn_expn.
rewrite exp_quo_lessE ?addr_ge0 ?mulr_ge0 ?invr_ge0 ?ler0n // muln1.
have: (1 + f%:~R^-1)%:C ^+ p <= (1 + f%:~R^-1)%:C ^+ (f.+1 * q).
  by rewrite exp_incr_expp ?ler1q ?lerDl ?invr_ge0 ?ler0n 1?ltnW ?ltn_ceil.
apply: le_trans.
rewrite lerXn2r ?nnegrE ?ler0q ?addr_ge0 ?mulr_ge0 ?invr_ge0 ?ler0n //.
rewrite ler_rat lerD2l ler_pdivrMr ?ltr0n // mulrC.
rewrite ler_pdivlMr ?ltr0n ?divn_gt0 //.
by rewrite -intrM ler_nat mulnC leq_trunc_div.

(* Second part : p < q *)
pose f := (q %/ p)%N.
have Helper0 : (0 < f)%N.
  by rewrite divn_gt0 // ltnW.
have Helper1 : 0 <= 1 + q%:Q / p%:Q.
  by rewrite addr_ge0 ?divr_ge0 ?ler0n.
have Helper2 : 1 + q%:Q / p%:Q <= 1 + (1 + f%:~R).
  rewrite lerD2l -mulrS ler_pdivrMr ?ltr0n // -natrM ler_nat.
  by rewrite ltnW ?ltn_ceil.
have Helper3 : (p * f <= q)%N.
  by rewrite mulnC leq_trunc_div.
apply: (@le_trans _ _ (exp_quo (1 + (1 + f%:Q)) p q)).
  by apply: exp_quo_less; rewrite // !addr_ge0 ?ler0n.
apply: (@le_trans _ _ (exp_quo (1 + (1 + f%:Q)) 1 f)).
  by apply: exp_quo_lessn; rewrite //= ?lerDl ?addr_ge0 ?ler0n // mul1n.
apply: (@le_trans _ _ (exp_quo ((3 ^ f.+1)%N%:Q) 1 f)).
  rewrite exp_quo_less // ?addr_ge0 ?ler0n //.
  by rewrite -rat1 -!natrD ler_nat !add1n replace_exponential.
rewrite /exp_quo expr1 !CratrE expnS natrM rootCMr ?ler0n //.
have -> : 9%:R = 3%:R * 3%:R :> algC by rewrite -natrM.
by rewrite ler_pM ?root_le_x ?rootC_ge0 ?ler0n ?natrX // ler_eXnr ?ler1n.
Qed.

End FourFacts.
