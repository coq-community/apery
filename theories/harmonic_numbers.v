(* A stub library on generalized harmonic numbers. *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import tactics shift bigopz.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* Definition of the generalized harmonic numbers, indexed by ints. *)
(* The first argument stays in nat. *)
Definition ghn (m : nat) (n : int) : rat :=
  \sum_(1 <= k < n + 1 :> int) (k %:Q ^ m)^-1.

Lemma ghn_Sn_inhom m n : n >= 0 ->
  ghn m (int.shift 1 n) = ghn m n + ((n%:Q + 1)^m)^-1.
Proof.
move=> pn. 
by rewrite /ghn int.shift2Z big_int_recr /= ?rmorphD //= -lerBlDr.
Qed.

Lemma ghn_small (m : nat) (n : int) : n <= 0 -> ghn m n = 0.
Proof. by move=> hn; rewrite /ghn big_geqz // gerDr. Qed.

Lemma ghn1 (m : nat) : ghn m 1 = 1.
Proof. by rewrite /ghn big_int_recr //= big_nil add0r exp1rz. Qed.

Lemma ghn_Sn2 m (n_ : int) (n := n_%:Q) :  n_ + 1 != 0 -> 
  ghn m (int.shift 2 n_) =
    ((n + 1) ^ m / (n + 2%:Q) ^ m + 1) * ghn m (int.shift 1 n_)
    - (n + 1) ^ m / (n + 2%:Q) ^ m * ghn m n_.
Proof.
move=> pn2.
case: (leP n_ 0) => hn.
  rewrite [in X in _ = _ - X]ghn_small // mulr0 subr0.
  rewrite {}/n; case: n_ pn2 hn => [ [] //  _ _ | n hn2].
    rewrite -[int.shift  2 0]/(int.shift 1 (int.shift 1 0)) [LHS]ghn_Sn_inhom //.
    by rewrite !int.shift2Z !add0r exp1rz mulrDl !mul1r addrC ghn1 mulr1.
  case: n hn2 => [| n] hn //.
  by rewrite !ghn_small ?mulr0 // NegzE int.shift2Z addrC !subzSS add0r oppr_le0.
rewrite ?ghn_Sn_inhom ?ltW ?addr_gt0 //=.
rewrite int.shift2R -/n.
move: (ghn m n_) => x.
apply/eqP; rewrite -subr_eq0 -!addrA addr_eq0; apply/eqP.
elim: m => [|m ->]; first by field => //.
(* The ring tactic is not able to reason under (_ ^ m) where m is a variable:
   we have to expand (_ ^_.+1) and identify p2 and p3 by hand... *)
rewrite !exprSz.
by field; rewrite /= !expfz_eq0; ring_lia.
Qed.
