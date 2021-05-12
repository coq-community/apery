From mathcomp Require Import all_ssreflect all_algebra.

Require Import binomialz bigopz.
Require Import seq_defs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope ring_scope.

(*** Properties of the sequence s: majorization of its values. ***)

(* FIXME : to be cleaned up *)
Lemma s_maj (i i0 : nat) : 0 < i%:~R :> rat -> (i0 <= i)%N ->
                      `|s i i0| <= i0%:~R / (2%:~R * i%:~R ^ 2) :> rat.
Proof.
  move=> bigi1 lei0i; apply: le_trans (ler_norm_sum _ _ _) _.
  rewrite -PoszD eq_big_int_nat /=.
  pose U (i1 : nat) := i1%:~R ^ 3 * binomialz i i1 * binomialz (Posz i + i1) i1.
  suff philippe (i1 : nat) : (0 < i1)%N -> (i1 <= i)%N -> i%:~R ^ 2 <= U i1.
    have -> : i0%:~R / (2%:~R * i%:~R ^ 2) =
              \sum_(1 <= i1 < i0 + 1) 1 / (2%:~R * i%:~R ^ 2) :> rat.
      rewrite -mulr_suml big_const_nat; congr (_ / _).
      rewrite addnK; elim: i0 {lei0i} => // n ihn /=.
      by  rewrite -ihn -addn1 PoszD rmorphD /= addrC.
    rewrite [X in X <= _]big_nat_cond [in X in _ <= X]big_nat_cond.
    apply: ler_sum=> j; rewrite andbT; case/andP=> h0j; rewrite addn1 => hji.
    have dpos : 0 < 2%:~R * j%:~R ^ 3 * binomialz i j * binomialz (Posz i + j) j.
      rewrite mulr_gt0 //; last by rewrite binz_gt0 // cpr_add.
      rewrite mulr_gt0 // ?binz_gt0 //; last exact: leq_trans lei0i.
      by rewrite mulr_gt0 // exprz_gt0 // -[0]/(0%:~R) ltr_nat.
    rewrite /d normrM normfV normrX expr1n !div1r gtr0_norm //.
    rewrite lef_pinv //; last by rewrite posrE mulr_gt0 // mulr_gt0.
    rewrite -2!mulrA ler_pmul2l // mulrA; apply: philippe => //.
    exact: leq_trans lei0i.
  move=> lt0i1; rewrite {}/U leq_eqVlt; case/orP=> [/eqP-> | hii1].
    rewrite !binz_nat_nat binn mulr1 -!mulrA mulrA ler_pmulr ?mulr_gt0 //.
    rewrite -rmorphM /= -[1]/(1%:~R) ler_nat muln_gt0.
    by move: bigi1; rewrite -[0]/(0%:~R) ltr_nat=> ->; rewrite bin_gt0 leq_addl.
  suff h : i1%:~R ^ 3 * i%:~R * i%:~R <=
           i1%:~R ^ 3 * binomialz i i1 * binomialz (Posz i + i1) i1.
    apply: le_trans h; rewrite -mulrA ler_pmull; last exact: mulr_gt0.
    rewrite [_ ^ _.+1]exprS expr2 -!rmorphM /= -[Z in Z <= _]/(1%:~R).
    by rewrite ler_nat !muln_gt0 !andbb.
  rewrite -2!mulrA ler_pmul2l; last first.
    by apply: exprz_gt0; rewrite -[0]/(0%:~R) ltr_nat.
  suff maj : i%:~R <= binomialz i i1.
    apply: ler_pmul; [exact: ltW | exact: ltW | exact: maj |].
    apply: le_trans maj _; rewrite !binz_nat_nat ler_nat; apply: leq_bin2l.
    by rewrite leq_addr.
  rewrite binz_nat_nat ler_nat.
  (* FIXME : n <= 'C(n, m) should be a lemma *)
  elim: i {bigi1 lei0i} hii1 => // n ihn; rewrite ltnS.
  rewrite leq_eqVlt; case/orP=> [/eqP -> | hi1n]; first by rewrite binSn.
  apply: leq_ltn_trans (ihn hi1n) _; case: i1 hi1n lt0i1 {ihn} => // i1 hi1n _.
  rewrite binS -[X in (X < _)%N]addn0 ltn_add2l bin_gt0; apply: leq_trans hi1n.
  exact: leq_trans (leqnSn _).
Qed.
