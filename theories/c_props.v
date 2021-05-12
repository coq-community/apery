From mathcomp Require Import all_ssreflect all_algebra.

Require Import binomialz lia_tactics.
Require Import seq_defs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope ring_scope.

(**** Properties of the sequence c ****)

Fact lt_0_c (i j : int) : 0 <= j <= i -> 0 < c i j.
Proof.
case/andP=> h0j hji; rewrite /c -expfzMl; apply: exprz_gt0.
by apply: mulr_gt0; apply: binz_gt0 => //; goal_to_lia; intlia.
Qed.

(* c is monotonic wrt its first argument *)
Fact c_incr (n m i : int) : 0 <= n -> 0 <= i -> i <= n -> n <= m ->
                            c n i <= c m i.
Proof.
case: n => // n _; case: i => // i _ lein; case: m => // m lenm; rewrite /c.
rewrite -!PoszD !binz_nat_nat -!expfzMl -!rmorphM /= !exprz_pintl // ler_nat.
by apply: leq_mul; apply: leq_mul; apply: leq_bin2l => //; rewrite leq_add2r.
Qed.

