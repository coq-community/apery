From mathcomp Require Import all_ssreflect all_algebra all_field.

Require Import arithmetics multinomial floor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import field_tactics.
Require Import bigopz.
Require Import lia_tactics conj.
Require Import shift.
Require Import extra_mathcomp.

Require Import hanson_elem_arith.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Section AlgCMissing.

Implicit Types x y z : algC.
  
Lemma root_le_x s x y : (0 < s)%N -> (0 <= x) -> (0 <= y) ->
                        (x <= y ^+ s) -> ((s.-root x) <= y) .
Proof.
move => Hs Hx Hy Hxys.
suff : (s.-root x) ^+ s <= y ^+ s.
  rewrite ler_pexpn2r // .
  by rewrite nnegrE rootC_ge0 // rootCK.
by rewrite rootCK.
Qed.

Lemma root_x_le s x y : (0 < s)%N -> (0 <= x) -> (0 <= y) ->
                        (x ^+ s <= y) -> (x <= s.-root y) .
Proof.
move => Hs Hx Hy Hxys.
suff : x ^+ s <= (s.-root y) ^+ s.
  rewrite ler_pexpn2r // .
  by rewrite nnegrE rootC_ge0 // rootCK.
by rewrite rootCK.
Qed.

Lemma rootC_leq m n x (Hx : 1 <= x) (Hn : (0 < n)%N) (Hmn : (m >= n)%N) : m.-root x <= n.-root x.
Proof.
have Hmgt0 : (0 < m)%N.
  by rewrite (leq_trans _ Hmn).
have Heq p s q (Hp : (p <= q)%N) : s.-root x ^+ q = s.-root x ^+ p * s.-root x ^+ (q - p).
  by rewrite -GRing.exprD subnKC.
suff Hm : (m.-root x) ^+ m <= (n.-root x) ^+ m.
  apply: root_x_le => // .
  - by rewrite rootC_ge0 ?(ler_trans _ Hx).
  - by rewrite ?(ler_trans _ Hx).
  - suff Hinterm :  m.-root x ^+ n <=  m.-root x ^+ m.
      by rewrite (ler_trans Hinterm) // rootCK ?lerr //.
    rewrite (Heq n m m) // ler_pmulr // .
      by rewrite exprn_ege1 // rootC_ge1.
    by rewrite exprn_gt0 //  rootC_gt0 // (ltr_le_trans _ Hx).
rewrite rootCK // (Heq n n m) // rootCK // ler_pmulr // ?(ltr_le_trans _ Hx) //.
by rewrite exprn_ege1 // rootC_ge1.
Qed.

(* Not sure if actually needed in library, but this lemma is helpful
to prove one_plus_invx_expx below *)
Lemma le_mrootn_n (m n : nat) : m.+1.-root n.+1%:R <= ratr n.+1%:~R :> algC.
apply: root_le_x => // .
* by rewrite ler0n.
* by rewrite CratrE /= CratrE /= ler0n.
* rewrite CratrE /= CratrE /=;  apply lter_eexpr => // .
  by rewrite ler1n.
Qed.

Lemma prod_root m n x : (0 < m)%N -> (0 < n)%N -> (0 <= x) ->
                        (m * n)%N.-root x = m.-root (n.-root x).
Proof.
move => Hm Hn Hx.
have Hmnpos : (0 < m * n)%N.
  by rewrite muln_gt0 Hm Hn.
have Hmn : (m * n).-root x \is Num.nneg.
  by rewrite nnegrE rootC_ge0 //.
suff: ((m * n).-root x) ^+ (m*n)%N = (m.-root (n.-root x)) ^+ (m * n)%N.
  apply: pexpIrn => // .
  by rewrite nnegrE rootC_ge0 //; rewrite rootC_ge0 // .
by rewrite rootCK // GRing.exprM rootCK // rootCK.
Qed.

End AlgCMissing.

Notation "r '%C'" := (ratr r : algC) (at level 8). (* random level *)

(* Section presenting the theory of exp_quo, which corresponds to
taking a rational exponent of a complex algebraic number *)
Section RationalPower.



Definition exp_quo r p q := (q.-root (r%C)) ^+ p.

Arguments exp_quo r p%nat q%nat : simpl never.

Lemma exp_quo_less r1 r2 p q : (0 < q)%N -> (0 <= r1) -> (0 <= r2) -> (r1 <= r2) -> (exp_quo r1 p q) <= (exp_quo r2 p q).
Proof.
move => Hq H1 H2 Hleq.
apply: ler_expn2r; last first.
- rewrite ler_rootCl ?ler_rat // .
  by rewrite nnegrE ler0q.
- by rewrite nnegrE rootC_ge0 // ler0q.
- by rewrite nnegrE rootC_ge0 // ler0q.
Qed.

Lemma exp_quo_1 p q : (0 < q)%N -> exp_quo 1 p q = 1.
Proof.
move => Hq; rewrite /exp_quo.
suff -> : q.-root (ratr 1) = 1 :> algC by rewrite expr1n.
by rewrite rmorph1 rootC1.
Qed.

Lemma exp_quo_lessn r1 p1 q1 p2 q2 :
  (0 < q1)%N -> (0 < q2)%N -> (1 <= r1) ->
  (p1 * q2 <= p2 * q1)%N ->
  (exp_quo r1 p1 q1) <= (exp_quo r1 p2 q2).
Proof.
move => Hq1 Hq2 H1r Hle.
have H0r : (0 <= r1).
  by apply: (ler_trans _ H1r); exact: ler01.
have Hprodpos : (0 < q1 * q2)%N.
  by rewrite muln_gt0 Hq1 Hq2.
suff :
  (q1.-root (ratr r1) ^+ p1) ^+ (q1 * q2)%N <=
  (q2.-root (ratr r1) ^+ p2) ^+ (q1 * q2)%N :> algC.
rewrite ler_pexpn2r //.
- by rewrite nnegrE; apply: exprn_ge0; rewrite rootC_ge0 // ?ler0q.
- by rewrite nnegrE; apply: exprn_ge0; rewrite rootC_ge0 // ?ler0q.
rewrite -exprM mulnCA exprM rootCK //.
rewrite -[in X in _ <= X]exprM.
have -> : (p2 * (q1 * q2) = q2 * (p2 * q1))%N.
  by rewrite [(q1*q2)%N]mulnC -mulnCA.
rewrite !exprM ![in X in _ <= X]rootCK // -!exprM.
rewrite ler_eqVlt in H1r.
case/orP: H1r.
- case/eqP => <-; by rewrite rmorph1 !expr1n lerr.
- by move => H1r; rewrite ler_eexpn2l // ltr1q.
Qed.


Lemma exp_quo_r_nat r i : (r ^+ i)%C = exp_quo r i 1.
Proof.
rewrite /exp_quo root1C.
by rewrite CratrE /=.
Qed.

Lemma exp_quo_nat_nat i j : (i ^ j)%N%:R%C = exp_quo (i%N%:Q) j 1.
Proof.
by rewrite natrX exp_quo_r_nat.
Qed.

Lemma exp_quo_mult_distr r1 r2 p1 q1 (Hr2 : 0 <= r2) :
  exp_quo r1 p1 q1 * exp_quo r2 p1 q1 = exp_quo (r1 * r2) p1 q1.
Proof.
rewrite /exp_quo.
rewrite rmorphM /=.
by rewrite [in RHS] rootCMr ?GRing.exprMn ?ler0q.
Qed.


Lemma exp_quo_plus r1 p1 q1 p2 q2 :
  (0 < q1)%N ->
  (0 < q2)%N ->
  (0 <= r1) ->
  exp_quo r1 (p1 * q2 + p2 * q1)%N (q1 * q2)%N =
  exp_quo r1 p1 q1 * exp_quo r1 p2 q2.
Proof.
move => Hq1pos Hq2pos Hr1pos.
have Hprodpos : (0 < q1 * q2)%N.
  by rewrite muln_gt0 Hq1pos Hq2pos.
rewrite /exp_quo.
set t1 := LHS.
set t2 := RHS.
suff: t1 ^+ (q1 * q2)%N = t2 ^+ (q1 * q2)%N.
  rewrite /t1 /t2.
  apply: pexpIrn => // .
  + by rewrite nnegrE; apply: exprn_ge0; rewrite rootC_ge0 ?ler0q //.
  + by rewrite nnegrE; apply mulr_ge0; apply: exprn_ge0;
      rewrite rootC_ge0 // ler0q.
rewrite /t1 /t2 -GRing.exprM mulnDl GRing.exprD.
have -> : ((p1 * q2 * (q1 * q2)) = (q1 * q2 * (p1 * q2)))%N.
  by rewrite mulnCA [(p1 * q2)%N]mulnC -!mulnA [(p1 * q2)%N]mulnC.
have -> : ((p2 * q1 * (q1 * q2)) = (q1 * q2 * (p2 * q1)))%N.
  by rewrite mulnC.
rewrite prod_root ?ler0q // ![in LHS]GRing.exprM rootCK // rootCK // .
rewrite ![in RHS]GRing.exprMn.
rewrite -!exprM. rewrite [in RHS]mulnC -[(p2 * _)%N]mulnC.
rewrite [X in (p2* X)%N]mulnC [(p2* (_ * _))%N]mulnCA ![in RHS]exprM !rootCK //.
rewrite -![in RHS]GRing.exprM. rewrite {1}mulnC; congr (_ * _).
by rewrite mulnC.
Qed.

Lemma exp_quo_equiv r1 p1 q1 p2 q2 :
  (0 < q1)%N ->
  (0 < q2)%N ->
  (0 <= r1) ->
  (p1 * q2 = p2 * q1)%N ->
  exp_quo r1 p1 q1 = exp_quo r1 p2 q2.
Proof.
move => Hq1pos Hq2pos Hr1pos Heq.
have Hprodpos : (0 < q1 * q2)%N.
  by rewrite muln_gt0 Hq1pos Hq2pos.
suff :
  (q1.-root (ratr r1) ^+ p1) ^+ (q1 * q2)%N =
  (q2.-root (ratr r1) ^+ p2) ^+ (q1 * q2)%N :> algC.
apply: pexpIrn => // .
- by rewrite nnegrE; apply: exprn_ge0; rewrite rootC_ge0 // ?ler0q // .
- by rewrite nnegrE; apply: exprn_ge0; rewrite rootC_ge0 // ?ler0q // .
rewrite -!exprM mulnC mulnA -Heq.
rewrite 2!exprM rootCK // .
by rewrite -mulnA -mulnCA 2!exprM rootCK // -!exprM mulnC.
Qed.

Lemma exp_quo_ge0 r p q :
  (0 < q)%N ->
  (0 <= r) ->
  0 <= exp_quo r p q.
Proof.
by move => Hq Hr; rewrite exprn_gte0 // ?rootC_ge0 // ler0q.
Qed.

Lemma exp_quo_gt0 r p q :
  (0 < q)%N ->
  (0 < r) ->
  0 < exp_quo r p q.
Proof.
by move => Hq Hr; rewrite exprn_gte0 // ?rootC_gt0 // ?ltr0q.
Qed.

Lemma exp_quo_ge1 r p q :
  (0 < q)%N ->
  (1 <= r) ->
  1 <= exp_quo r p q.
Proof.
by move => Hq Hr; rewrite exprn_ege1 // ?rootC_ge1 // ler1q.
Qed.

Lemma exp_quo_gt1 r p q :
  (0 < p)%N ->
  (0 < q)%N ->
  (1 < r) ->
  1 < exp_quo r p q.
Proof.
by move => Hp Hq Hr; rewrite exprn_egt1 // ?rootC_gt1 // ?ltr1q // -lt0n.
Qed.

Lemma exp_quo_self_grows (p1 q1 p2 q2 : nat) r1 r2 :
  (0 < q1)%N ->
  (0 < q2)%N ->
  (r1 = p1%:Q / q1%:Q) ->
  (r2 = p2%:Q / q2%:Q) ->
  (0 < r1) ->
  (1 <= r2) ->
  (r1 <= r2) ->
  exp_quo r1 p1 q1 <= exp_quo r2 p2 q2.
Proof.
move => Hq1 Hq2 Hr1 Hr2 Hr1gt0 Hle1r2 Hle12.
have Hr1pos : 0 <= r1.
  exact: ltrW.
have Hr2pos : 0 <= r2.
  by rewrite Hr2 divr_ge0 // ?ler0z.
have Hprodpos : (0 < q1 * q2)%N.
  by rewrite muln_gt0 Hq1 Hq2.
have Hleq : (p1 * q2 <= p2 * q1)%N.
  suff HQ : p1%:Q * q2%:Q <= p2%:Q * q1%:Q.
  by rewrite -!intrM ler_int in HQ.
  rewrite -ler_pdivl_mulr ?ltr0z //.
  rewrite [p2%:~R * _]mulrC -mulrA -ler_pdivr_mull ?ltr0z // mulrC.
  by move: Hle12; rewrite Hr1 Hr2.
have -> :
  exp_quo r2 p2 q2 =
  exp_quo r2 p1 q1 * exp_quo r2 (p2 * q1 - p1 * q2)%N (q1 * q2)%N.
  rewrite -exp_quo_plus //.
  apply: exp_quo_equiv => // .
    by rewrite !muln_gt0 Hq1 Hq2.
  rewrite !mulnA.
  rewrite mulnBl mulnDl mulnBl //.
  have -> : (p1 * q1 * q2 * q2 = p1 * q2 * q1 * q2)%N.
    by congr muln; rewrite mulnAC.
  rewrite subnKC // .
  by rewrite -mulnA -[X in (_ <= X)%N]mulnA leq_mul.
have -> : exp_quo r2 p1 q1 = exp_quo r1 p1 q1 * exp_quo (r2 / r1) p1 q1.
  rewrite exp_quo_mult_distr ?divr_ge0 // .
  congr exp_quo.
  rewrite mulrCA divrr ?mulr1 //.
  exact: unitf_gt0.
rewrite -{1}[exp_quo _ _ _]mulr1.
rewrite -mulrA.
apply: ler_pmul => // ; try rewrite ler01 // .
  exact: exp_quo_ge0.
rewrite -[1]mulr1.
apply: ler_pmul => // ; try rewrite ler01 // .
  apply: exprn_ege1; rewrite rootC_ge1 //.
  rewrite rmorphM /= CratrE /=.
  rewrite ler_pdivl_mulr ?ltr0q ?mul1r //.
  by rewrite ler_rat.
apply: exprn_ege1. rewrite rootC_ge1 //.
suff -> : 1 = ratr (1%N%:Q).
  by rewrite ler_rat.
move => t; by rewrite ratr_int.
Qed.

Lemma sqrtC_exp_quo (r : rat) : sqrtC r%C = exp_quo r 1%N 2%N.
Proof.
by rewrite /exp_quo expr1.
Qed.

(* Unused lemma, but might still be of use somewhere else *)
Lemma bound_exp_imp_bound_root a b v p (Hp : (0 < p)%N) :
  0 <= a ->
  0 <= b  ->
  a ^+ p <= v <= b ^+ p  ->
  ratr a <= exp_quo v 1 p <= ratr b.
Proof.
move => Hage0 Hbge0 ; move/andP => [Hge Hle].
have Ha : a%C \is Num.nneg.
  by rewrite nnegrE ler0q.
have Hvge0 : (0 <= v).
  by rewrite (ler_trans _ Hge) // exprn_ge0.
have Hb : b%C \is Num.nneg.
  by rewrite nnegrE ler0q.
have Hprootv : (p.-root (ratr v) : algC) \is Num.nneg.
  by rewrite nnegrE rootC_ge0 // ler0q.
apply/andP; split.
have HgeC : (a ^+ p)%C <= v%C by rewrite ler_rat.
move: HgeC.
by rewrite -[ratr v](rootCK Hp) /exp_quo CratrE /= ler_pexpn2r // .
have HgeC : v%C <= (b ^+ p)%C by rewrite ler_rat.
move: HgeC.
rewrite -[ratr v](rootCK Hp) /exp_quo CratrE /= ler_pexpn2r // .
Qed.

End RationalPower.

(* This Section contains a collection of four facts used in the proof
of Hanson's lemma: a comparison of factorial to a geometric sequence,
the formula for summing a geometric sequence, and a bound on (1 + 1 /
x) ^ x *)
Section FourFacts.

(* A lemma comparing factorial to a geometric sequence *)
Lemma fact_greater_geom i : i.+1`!%:~R >= (3%:Q / 2%:~R) ^+ i.
Proof.
elim: i => [|i HIi]; first by rewrite expr0.
rewrite exprS factS PoszM intrM.
have frac_ge0 :  0 <= 3%:Q / 2%:~R.
  by apply: divr_ge0; rewrite ler0z.
have fracpow_ge0 :  0 <= (3%:Q / 2%:~R) ^+ i.
  by rewrite exprn_ge0 ?frac_ge0.
suff : 0 <= 3%:~R / 2%:Q <= i.+2%:~R /\ 0 <= (3%:~R / 2%:Q) ^+ i <= (i.+1)`!%:~R.
  case => [] /andP [H1 H2] /andP [H3 H4]; exact: ler_pmul.
split; apply/andP; split.
  - exact: frac_ge0.
  - rewrite ler_pdivr_mulr; last by rewrite ltr0n.
    apply: (@ler_trans _ (2%:~R * 2%:~R)).
      by rewrite -rmorphM /= ler_nat.
    apply: ler_pmul; rewrite ?ler0n; try exact: isT.
    rewrite -[i.+2]addn2 -{1}[2]add0n !PoszD !intrD .
    apply: ler_add; rewrite ?ler_nat; try exact: isT.
  - exact: fracpow_ge0.
  - exact: HIi.
Qed.

(* Formula for a geometric sum in a field *)
Lemma geometric_sum (R : numFieldType) n (r : R) (Hr : 1 - r != 0) :
  \sum_(i < n) r ^+ i = (1 - r ^+ n) / (1 - r).
Proof.
elim: n => [|n Hn].
  by rewrite big_ord0 expr0 subrr mul0r.
suff: (1 - r ^+ n) / (1 - r) + r ^+ n = (1 - r ^+ n.+1) / (1 - r).
  by rewrite big_ord_recr /= Hn.
have H1neq0 :  (1 : R) != 0 by exact: GRing.oner_neq0.
rewrite -[r ^+ n]divr1 GRing.addf_div // !mulr1 !divr1; congr (_ / _).
rewrite -[- r ^+n]GRing.mulrN1 -addrA -mulrDr.
have -> : -1 + (1 - r) = - r by rewrite addrA [-1 + 1]addrC subrr sub0r.
by rewrite mulrN exprSr.
Qed.

(* A bound on (1 + 1 / (n+1)) ^ (n+2) *)
Lemma one_plus_invn_expn (n : nat) : ((1%:Q + (1%:Q / n.+1%:Q)%Q) ^+ n.+2 <= 8%:Q).
Proof.
rewrite exprDn.
suff H1 :
  \sum_(i < n.+3) 1%:~R ^+ (n.+2 - i) * (1%:~R / n.+1%:~R)%Q ^+ i *+ 'C(n.+2, i)
  <= 2%:~R * \sum_(i < n.+2) 1%:~R / ((factorial i)%:~R).                          apply: (ler_trans H1).
  suff He_leq_4 : (\sum_(i < n.+2) 1%:~R / i`!%:~R) <= 4%:Q.
    apply: (@ler_trans _ (2%:Q * 4%:Q)) => // .
    apply: ler_pmul => // .
    have {1}-> : 0%R = \sum_(i < n.+2) 0%:Q.
      by rewrite big1.
    by apply: ler_sum => i _; rewrite divr_ge0 // ler0n.
  apply: (@ler_trans _ (1 + \sum_(i < n.+1) (2%:Q / 3%:Q) ^+ i)).
    rewrite big_ord_recl /= fact0.
    apply: ler_add => // .
    apply: ler_sum => i _ /= .
    case: i => i Hi; rewrite /bump /= .
    rewrite ler_pdivr_mulr; last (rewrite ltr0z; exact: fact_gt0).
    rewrite -ler_pdivr_mull; first rewrite mulr1.
      rewrite -GRing.exprVn.
      have -> : (2%:Q / 3%:Q)^-1 = (3%:Q / 2%:Q) by [].
      exact: fact_greater_geom.
    exact: exprn_gt0.
  rewrite geometric_sum // .
  suff Hgeom_small (i : nat) : (2%:~R / 3%:~R) ^+ i <= 1%Q.
    have -> : 4%:Q = 1 + 3%:Q by [].
    apply: ler_add => // .
    apply: (@ler_trans _ (1 / (1 - 2%:Q / 3%:Q))) => // .
    apply: ler_pmul => // .
      rewrite subr_ge0.
      exact: Hgeom_small.
    rewrite ler_sub_addl -{1}[1]add0r.
    apply: ler_add => // .
    by rewrite exprn_ge0.
  by rewrite exprn_ile1 // .
rewrite -exprDn exprS.
apply: ler_pmul.
- by apply: addr_ge0 => //; apply: divr_ge0 => // ; apply: ler0z.
- rewrite exprn_ge0 // .
  by apply: addr_ge0 => //; apply: divr_ge0 => // ; apply: ler0z.
- change 2%:Q with (1%:Q + 1); apply: ler_add => // .
  rewrite ler_pdivr_mulr.
    by rewrite mul1r ler_int.
  exact: ltr0z.
- rewrite exprDn.
  apply: ler_sum => i _.
  rewrite expr1n mul1r.
rewrite lter_pdivl_mulr ?ltr0n ?fact_gt0 // .
rewrite -mulr_natl mulrC -mulrA.
rewrite -natrM bin_ffact.
rewrite expr_div_n expr1n div1r mulrC ler_pdivr_mulr -natrX ?ltr0n ?expn_gt0 //.
rewrite mul1r ler_nat.
exact: ffact_le_expn.
Qed.

(* this proof is very long in big part because of exp_quo *)
Lemma one_plus_invx_expx (p q : nat) (r : rat) (n : nat) :
  (0 < r) -> (r = p%:Q / q%:Q) -> (exp_quo (1%:Q + 1 / r) p q <= (ratr 9%N%:Q)).
Proof.
move => Hrpos Hrpq.
have Hp : (0 < p)%N.
  apply: negbNE; apply/negP => Habs.
  rewrite -eqn0Ngt in Habs. move/eqP in Habs.
  rewrite Habs /= mul0r in Hrpq.
  by rewrite Hrpq in Hrpos.
have Hq : (0 < q)%N.
  apply: negbNE; apply/negP => Habs.
  rewrite -eqn0Ngt in Habs. move/eqP in Habs.
  rewrite Habs /= invr0 mulr0 in Hrpq.
  by rewrite Hrpq in Hrpos.
have Hle01 : 0 <= 1 :> algC by exact: ler01.
have Hle0r : 0 <= ratr r :> algC by apply: ltrW; rewrite ltr0q.
case/orP: (ger_leVge Hle01 Hle0r) => [H1r|Hr1].

(* First part : 1 <= r *)
have := (floorQ_spec r).
set f := floorQ r => Hfloor.
have Hfnat : f \is a Znat.
by rewrite Znat_def; apply: floorQ_ge0; apply: ltrW.
move/ZnatP: Hfnat => [] m Hfm.
case/andP: Hfloor => [Hf1 Hf2].
apply (@ler_trans _ (ratr 8%N%:Q)); last  by rewrite ler_rat.
have Hle1m : (1 <= m)%N.
by rewrite ler1q in H1r; have := (floorQ_ge1 H1r); rewrite -/f Hfm.

have Hfloor_inv : (1%:Q / (f%:Q+1)) < 1%:Q / r <= 1 / f%:Q.
  apply/andP; split.
    rewrite ltr_pdivr_mulr.
      rewrite mulrC mulrA.
      rewrite ltr_pdivl_mulr // mul1r mulr1.
      exact: Hf2.
    rewrite ltr_paddl // ler0z // .
    by apply: floorQ_ge0; apply: ltrW.
  rewrite ler_pdivr_mulr // .
  rewrite mulrC mulrA.
  rewrite ler_pdivl_mulr // ?mul1r ?mulr1 ?ltr0z // .
  apply: ltr_le_trans; last first.
    apply floorQ_ge1. (* apply: does not work *)
    by rewrite ler1q in H1r.
  exact: ltr01.

(* a few helpers which will be needed in the intermediate steps *)
have Helper1 : 0 <= r by exact: ltrW.
have Helper2 : 0 <= 1 / r by rewrite divr_ge0 // .
have Helper3 : 0 <= 1%:~R + 1 / r.
  exact: addr_ge0 => // .
have Helper4 : 0 <= 1 / f%:Q.
  by rewrite divr_ge0 //  Hfm ler0n.
have Helper5 : 0 <= 1%:~R + 1 / f%:Q.
  by rewrite addr_ge0.
have Helper6 : 1 <= 1%:~R + 1 / f%:Q.
  by rewrite ler_addl.

suff Hinterm : exp_quo (1%:~R + 1 / r) p q <= exp_quo (1%:Q + 1 / f%:Q) m.+1 1.
  apply: (ler_trans Hinterm).
  rewrite Hfm.
  case: m Hfm Hinterm Hle1m => [| m] Hfm Hinterm // Hle1m.
  rewrite -exp_quo_r_nat ler_rat.
  exact: one_plus_invn_expn.
apply: ler_trans.
  apply (@exp_quo_less _ (1%:~R + 1 / f%:~R)) => // .
  apply: ler_add; first by rewrite lerr.
  by case/andP: Hfloor_inv.
apply exp_quo_lessn => // .
rewrite muln1.
move: Hf2.
have -> : (f%:~R + 1)%Q = (f + 1)%:Q.
  by rewrite rmorphD /=.
rewrite Hrpq ltr_pdivr_mulr ?ltr0z // -intrM Hfm -PoszD -PoszM.
by rewrite ltr_nat addn1; exact: leqW.

(* r <= 1 *)
have := (floorQ_spec (r^-1)).
set f := floorQ r^-1 => Hfloor.
have Hfnat : f \is a Znat.
  rewrite Znat_def; apply: (@ler_trans _ 1); first by rewrite ler01.
  apply: floorQ_ge1; rewrite invr_ge1 //.
    by rewrite lerq1 in Hr1.
  exact: unitf_gt0.
move/ZnatP: Hfnat => [] m Hfm.
case/andP: Hfloor => [Hf1 Hf2].

have Helper0 : 0 < f%:Q.
  apply: (@ltr_le_trans _ 1%:Q); last first.
    rewrite /f ler_int; apply floorQ_ge1. rewrite invr_ge1;
                                            rewrite lerq1 // in Hr1.
    exact: unitf_gt0.
    exact: ltr01.
have Helper1 : (0 < m)%N.
  suff: 0 < m%:Q by rewrite ltr0n.
  by rewrite -Hfm.

have Helper2 : 0 < f%:Q + 1.
  apply: (ltr_le_trans (ltr01)).
    by rewrite ler_addr Hfm ler0n.
have Helper3 :   r <= 1 / f%:~R.
  rewrite ler_pdivl_mulr // mulrC  -ler_pdivl_mulr ?div1r //.
have Helper4 : 0 <= 1%:~R + 1 / r.
  apply: (@ler_trans _ (1 + f%:~R)).
  by rewrite addrC; apply: ltrW.
  by apply: ler_add => // ; rewrite div1r.
have Helper5 :  0 <= 1%:~R + (1 + f%:~R)%Q.
  by rewrite Hfm -{2}rat1 addrA -!intrD ler0n.
have Helper6 : 1%:~R + 1 / r <= 1%:~R + (1 + f%:~R)%Q.
  rewrite Hfm -{2}rat1 ler_add // .
  by rewrite div1r -Hfm; apply: ltrW; rewrite addqC.
have Helper7 : 1 <= 1%:~R + (1 + f%:~R)%Q.
  by rewrite Hfm -{3}rat1 addrA -!intrD ler1n.
have Helper8 :   (p * m <= q)%N.
  move: Hf1; rewrite Hfm Hrpq invrM ?invrK.
  + rewrite ler_pdivl_mulr.
      by rewrite mulrC -intrM ler_int lez_nat.
    by rewrite ltr0z.
  + by rewrite unitf_gt0 // ltr0z.
  + by rewrite unitf_gt0 // invr_gt0 ltr0z.

have Hfloor_inv : (1%:Q / (f%:Q+1)) < r <= 1 / f%:Q.
  apply/andP; split => // .
  rewrite ltr_pdivr_mulr // .
  rewrite -ltr_pdivr_mull ?mulr1 // .
  apply: (@ler_trans _ (exp_quo (1%:~R + (1 + f%:~R)%Q) p q)).
    exact: exp_quo_less.
  apply: (@ler_trans _ (exp_quo (1%:~R + (1 + f%:~R)%Q) 1 m)); last first.
    apply: (@ler_trans _ (exp_quo (((3 ^ (m.+1))%N)%:Q) 1 m)).
      apply exp_quo_less => // .
        exact: ler0n.
      rewrite -{2}rat1 addrA Hfm -!intrD ler_nat -addnA [(1+m)%N]addnC addn1.
      exact: (replace_exponential m.+1).
    rewrite /exp_quo expr1 CratrE /= CratrE /= /= expnS natrM rootCMr // .
      have -> : 9%:Q%C = ratr (3%:Q) * ratr (3%:Q).
        by rewrite CratrE /= CratrE /= CratrE /= CratrE /= -natrM.
      rewrite ler_pmul // .
      + by rewrite rootC_ge0 // ler0n.
      + by rewrite rootC_ge0 // ler0n.
      + case: m Hfm Helper1 Helper8 => [|m]// _ _ _; exact: le_mrootn_n.
    (* TODO: make a lemma out of this *)
        * rewrite natrX exprCK // ?CratrE // ler0n //.
        * by rewrite ler0n.

apply: exp_quo_lessn; first exact: Hq; first exact: Helper1;
  first exact: Helper7.
rewrite mul1n; exact: Helper8.
Qed.

End FourFacts.
