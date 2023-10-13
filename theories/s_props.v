From mathcomp Require Import all_ssreflect all_algebra.
Require Import binomialz bigopz seq_defs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(*** Properties of the sequence s: majorization of its values. ***)

(* FIXME : to be cleaned up *)
Lemma s_maj (i i0 : nat) :
  0 < i%:Q -> (i0 <= i)%N -> `|s i i0| <= i0%:Q / (2%:Q * i%:Q ^ 2).
Proof.
move=> bigi1 lei0i; apply: le_trans (ler_norm_sum _ _ _) _.
rewrite -PoszD eq_big_int_nat /=.
pose U (i1 : nat) :=
  i1%:Q ^+ 3 * (binomialz i i1)%:Q * (binomialz (Posz i + i1) i1)%:Q.
suff philippe (i1 : nat) : (0 < i1)%N -> (i1 <= i)%N -> i%:Q ^+ 2 <= U i1.
  have ->: i0%:Q = \sum_(1 <= i1 < i0 + 1) 1.
    by rewrite big_const_nat addnK iter_addr_0.
  rewrite mulr_suml [X in X <= _]big_nat_cond [in X in _ <= X]big_nat_cond.
  apply: ler_sum => j; rewrite andbT addn1 ltnS => /andP [h0j hji].
  have dpos :
    0 < 2%:Q * j%:Q ^+ 3 * (binomialz i j)%:Q * (binomialz (Posz i + j) j)%:Q.
    by rewrite !mulr_gt0 ?ltr0z // binz_gt0 ?cprD //; exact: leq_trans lei0i.
  rewrite /d normrM normfV normrX expr1n !div1r gtr0_norm //.
  rewrite lef_pV2 //; last by rewrite posrE mulr_gt0 // mulr_gt0.
  by rewrite -2!mulrA ler_pM2l // mulrA; apply/philippe/leq_trans/lei0i.
move=> lt0i1; rewrite {}/U leq_eqVlt => /predU1P[->|hii1].
  rewrite !binz_nat_nat binn mulr1 -!mulrA mulrA ler_pMr ?mulr_gt0 //.
  by move: bigi1; rewrite -rmorphM ler1n muln_gt0 ltr0n bin_gt0 leq_addl andbT.
have: i%:Q ^+ 2 <= i1%:Q ^+ 3 * i%:Q ^+ 2.
  by rewrite ler_pMl ?exprn_gt0 // exprn_ege1 ?ler1z.
move/le_trans; apply; rewrite -mulrA ler_pM2l; last first.
  by rewrite exprn_gt0 ?ltr0n.
suff maj : Posz i <= binomialz i i1.
  apply: ler_pM; rewrite ?ler0n ?ler_int //; apply: le_trans maj _.
  by rewrite !binz_nat_nat lez_nat leq_bin2l ?leq_addr.
rewrite binz_nat_nat lez_nat.
(* FIXME : n <= 'C(n, m) should be a lemma *)
case: i1 lt0i1 hii1 {lei0i bigi1} => // i1 _.
elim: i i1 => [|i ihi] [|i1] //; rewrite ltnS ?bin1 // => hii1.
by rewrite binS -add1n leq_add ?bin_gt0 ?ihi.
Qed.
