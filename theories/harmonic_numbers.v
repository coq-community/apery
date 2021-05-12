(* A stub library on generalized harmonic numbers. *)
From mathcomp Require Import all_ssreflect all_algebra.

Require Import shift bigopz.
Require Import field_tactics.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope ring_scope.

(* Definition of the generalized harmonic numbers, indexed by ints. *)
(* The first argument stays in nat. *)
Definition ghn (m : nat) (n : int) : rat :=
  \sum_(1 <= k < n + 1 :> int) (k %:~R ^ m)^-1.

Lemma ghn_Sn_inhom m n : n >= 0 ->
  ghn m (int.shift 1 n) = ghn m n + ((n%:~R + 1)^m)^-1.
Proof.
move=> pn. 
rewrite /ghn int.shift2Z big_int_recr /= ?rmorphD //=.
by rewrite -ler_subl_addr.
Qed.

Lemma ghn_small (m : nat) (n : int) : n <= 0 -> ghn m n = 0.
Proof. by move=> hn; rewrite /ghn big_geqz // ger_addr. Qed.

Lemma ghn1 (m : nat) : ghn m 1 = 1.
Proof. by rewrite /ghn big_int_recr //= big_nil add0r exp1rz. Qed.

Lemma ghn_Sn2 m (n_ : int) (n := n_%:~R) :  n_ + 1 != 0 -> 
  ghn m (int.shift 2 n_) =
    ((n + 1) ^ m / (n + 2%:~R) ^ m + 1) * ghn m (int.shift 1 n_)
    - (n + 1) ^ m / (n + 2%:~R) ^ m * ghn m n_.
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
elim: m => [|m ->]; first by rat_field => //.
(* The ring tactic is not able to reason under (_ ^ m) where m is a variable:
   we have to expand (_ ^_.+1) and identify p2 and p3 by hand... *)
rewrite !exprSz.
set p1 := _ ^ _.
set p2 := _ ^ _.
rat_field.
rewrite /p1 /p2.

(* These two lemmas could be handled by a lia tactic. *)
have hn01 : n + 2%:~R != 0 :> rat.
  rewrite addr_eq0 -rmorphN /= -NegzE eqr_int.
  by apply/eqP => nD; move: hn; rewrite nD.

have hn02 : n + 1%:~R != 0 :> rat.
  rewrite addr_eq0 -rmorphN /= -NegzE eqr_int.
  by apply/eqP => nD; move: hn; rewrite nD.
by repeat split; apply/eqP; rewrite ?expfz_eq0 // negb_and ?hn01 ?hn02 orbT.
Qed.
