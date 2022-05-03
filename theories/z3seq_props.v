From mathcomp Require Import all_ssreflect all_algebra.
Require Import tactics bigopz harmonic_numbers seq_defs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(*** Properties of the sequence ghn3 ***)

(* In the sequel, instead of (ghn 3), we use z3seq, the partial series of *)
(* ghn3, indexed by a natural number *)
Definition z3seq (n : nat) := ghn3 (Posz n).

Fact z3seqE (n : nat) : z3seq n = \sum_(1 <= k < n.+1)(k%:Q ^ 3)^-1.
Proof.
by rewrite /z3seq /ghn3 /ghn -PoszD eq_big_int_nat /= addn1.
Qed.

Fact Dz3seqE (i j : nat) : (j <= i)%N ->
                   z3seq i - z3seq j = \sum_(j.+1 <= k < i.+1) (k%:Q ^ 3)^-1.
Proof.
rewrite -ltnS => leji; rewrite !z3seqE (big_cat_nat _ _ _ _ leji) //=.
by rewrite addrAC addrN add0r.
Qed.

Fact lt_0_Dz3seq (i j : nat) : (j < i)%N -> 0 < z3seq i - z3seq j.
Proof.
move=> ltji; rewrite Dz3seqE; last exact: ltnW.
rewrite big_nat_recr //=; apply: ltr_paddl; last first.
  by rewrite invr_gt0 exprn_gt0 // ltr0n; apply: leq_trans ltji.
by apply: sumr_ge0 => *; rewrite invr_ge0 exprn_ge0 // ler0n.
Qed.

(* Majoration of the summand 1 / k^3 of z3seq by the integral of 1 / x^3 *)
(* between (k - 1) and k, expressed using the primitive. This is a technical *)
(* step for showing the convergence of the series. *)
(* The proof is much longer than it should be because automation tools are *)
(* clumsy here. *)

(* FIXME: problem with intlia preprocessing : lt1r is badly converted and
     the hypothesis is not taken into account by lia if not generalized 
      beforehand. *)
Lemma z3seq_smd_maj (k : nat) : 0 < k%:Q ->
  (k.+1%:Q ^ 3)^-1 <= - 2%:Q^-1 * ((k.+1%:Q ^ 2) ^-1 - (k%:Q ^ 2) ^-1).
Proof.
move=> hr; set r := k.+1%:Q.
have hkr : k%:Q = r - 1 by rewrite /r -addn1 PoszD rmorphD addrK.
have hrk : r = k%:Q + 1 by rewrite hkr addrK.
have lt1r : 1 < r by rewrite hrk ltr_addr.
rewrite hkr; set  rhs := (X in _ <= X).
have {rhs} -> : rhs = 2%:Q^-1 * (2%:Q * r - 1) / (r - 1) ^ 2 * (r ^ 2)^-1.
  by rewrite /rhs; field; ring_lia.
have -> : (r ^ 3)^-1 = r ^-1 * (r ^ 2)^-1 by field; ring_lia.
have le0r : 0 <= r by apply: ltW; apply: lt_trans lt1r.
apply: ler_pmul; rewrite ?invr_ge0 ?exprn_ge0 //.
rewrite ler_pdivl_mulr; last first.
  by apply: exprz_gt0; rewrite subr_gt0.
rewrite ler_pdivr_mull; last by apply: lt_trans lt1r.
rewrite -subr_ge0; set rhs := (X in _ <= X).
have {rhs} -> : rhs = 3%:Q / 2%:Q * r - 1 by rewrite /rhs; field.
by rewrite subr_ge0; apply/mulr_ege1/ltW.
Qed.
