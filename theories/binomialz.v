Require Import Psatz.
From mathcomp Require Import all_ssreflect all_algebra.

Require Import field_tactics lia_tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope ring_scope.

(* A binomial function over signed integers*)
Fixpoint binomial_rec (n m : nat) (pn pm : bool) : rat :=
match m, pm with
| 0%N, true => 1
| _, false => 0
| m'.+1, true =>
  let fix auxm n0 pn0 :=
    match n0, pn0 with
    | 0%N, true => 0
    | n0'.+1, true => binomial_rec n0' m' pn0 pm + auxm n0' pn0
    | n0'.+1, false => auxm n0' pn0 - binomial_rec n0 m' pn0 pm
    | 0%N, false => - binomial_rec n0 m' pn0 pm
    end
  in auxm n pn
end.

(* Eval compute in (binomial_rec 5 3 false true).*)

Definition binomialz_ (n m : int) : rat :=
match n,m with
| Posz n1, Posz m1 => binomial_rec n1 m1 true true
| Negz n1, Posz m1 => binomial_rec n1 m1 false true
| Posz n1, Negz m1 => binomial_rec n1 m1 true false
| Negz n1, Negz m1 => binomial_rec n1 m1 false false
end.

Definition binomialz := nosimpl binomialz_.

(* Eval compute in binomialz 5 3.*)

(* Facts from the recursive code defining of binomialz. *)
Fact binz0 (n : int) : binomialz n 0 = 1.
Proof. by case: n => n /=; rewrite /binomialz /binomialz_ /=. Qed.

Fact binz_neg (n m : int) : m <= -1 -> binomialz n m = 0.
Proof. by case: m => m //= _; case: n => n; case: m. Qed.

Fact bin0z (m : int) : m >= 1 -> binomialz 0 m = 0.
Proof. by case: m => [ | m] // [ | m]. Qed.

Fact bin_posz_posz (n m : nat) :
  binomialz (Posz n.+1) (Posz m.+1) =
  binomialz (Posz n) (Posz m) + binomialz (Posz n) (Posz m.+1).
Proof. by []. Qed.

Fact bin_negz_posz (n m : nat) :
  binomialz (Negz n.+1) (Posz m.+1) =
  binomialz (Negz n) (Posz m.+1) - binomialz (Negz n.+1) (Posz m).
Proof. by []. Qed.

Fact bin_1N_posz (m : nat) :
  binomialz (Negz 0) (Posz m.+1) = - binomialz (Negz 0) (Posz m).
Proof. by []. Qed.

(* Now more relations, combining inductions with the previous rules. *)
Lemma bin_1N (m : int) : m >= 0 -> binomialz (Negz 0) m = (- 1) ^ m.
Proof.
case: m => m // _.
by elim: m => [ | m ihm] //; rewrite bin_1N_posz ihm exprSz mulN1r.
Qed.

Lemma Pascal_z (n m : int) :
  binomialz (n + 1) (m + 1) = binomialz n (m + 1) + binomialz n m.
Proof.
case: m => m; case: n => n /=;
  rewrite -?[Posz n + 1]PoszD -?[Posz m + 1]PoszD ?addn1.
- by rewrite bin_posz_posz addrC.
- case: n => [ | n] //=; first by rewrite bin_1N_posz addNr bin0z.
  by rewrite bin_negz_posz -addrA addNr addr0 NegzE addrC subzSS add0r -NegzE.
- case: m => [ | m]; first by rewrite subrr /= addr0.
  by rewrite NegzE addrC subzSS add0r -NegzE; case: m => [ | m].
- case: m => [ | m]; last by rewrite !binz_neg.
  by rewrite !binz0 binz_neg.
Qed.


(* Now we prove more (conditional) relations and values for binomialz *)

Lemma binz_nat_nat (n m : nat) : binomialz (Posz n) (Posz m) = 'C(n,m)%:~R.
Proof.
elim: n m => [ | n Hn] [ | n0] //;
  rewrite -[in LHS](addn1 n) -[in LHS](addn1 n0).
rewrite [Posz (n + 1)]PoszD [Posz (n0 + 1)]PoszD Pascal_z ['C(n.+1, n0.+1)]binS.
by rewrite !Hn !addn1 !PoszD rmorphD.
Qed.

Lemma binzE (m n : nat) : (m <= n)%N ->
  binomialz (Posz n) (Posz m) =
    (Posz n`!)%:~R / ((Posz m`!)%:~R * (Posz (n - m)`!)%:~R).
Proof.
move=> hmn; rewrite binz_nat_nat; apply/eqP.
set denom := (X in _ / X).
have side : denom != 0.
  by rewrite /denom -rmorphM pnatr_eq0 muln_eq0 negb_or -!lt0n !fact_gt0.
rewrite -(inj_eq (@mulIf _ denom _)) // divfK // /denom {side denom}.
by rewrite -!rmorphM -!PoszM /= bin_fact.
Qed.

Lemma binz_on_diag (n : int) : binomialz n n = (n >= 0)%:~R.
Proof.
case: n => n; last by rewrite binz_neg.
by rewrite binz_nat_nat // binn le0z_nat.
Qed.

(* A property to transfer relations that are first proved on nonnegative *)
(* upper argument of the binomial. *)
Lemma binNzz (n m : int) : binomialz n m = (- 1) ^ m * binomialz (m - n - 1) m.
Proof.
wlog: m n / n <= 0.
  move=> hwlog; case: (lerP n 0) => hn; first exact: hwlog.
  case:n hn => [ [ // | n]| //] _.
  case: m => m; last by rewrite !binz_neg // mulr0.
  case: (ltrP (Posz n.+1) (Posz m)) => hnm.
  - rewrite binz_nat_nat bin_small //.
    rewrite -addrA -opprB opprK subzn // binz_nat_nat bin_small ?mulr0 //.
    by rewrite add1n subnSK // leq_subLR leq_addl.
  - have {hnm} hnm : (Posz m) - (Posz n.+1) - 1 <= 0.
      rewrite subr_le0 ler_subl_addl; apply: le_trans hnm _.
      by rewrite ler_addl.
    rewrite [in RHS]hwlog //.
    rewrite opprB addrA addrAC -[Posz m + 1 - 1]addrA subrr addr0 opprB addrCA.
    by rewrite subrr addr0 mulrA -expfzMl exp1rz mul1r.
case: m => m; last by rewrite !binz_neg // mulr0.
case: n => [n | n _].
  case: n => [_ | //]; case:m => [ | m]; first by rewrite !binz0.
  by rewrite bin0z // subr0 subzSS subr0 binz_nat_nat bin_small // mulr0.
rewrite [in RHS]NegzE opprK -addrA subzSS subr0.
move: {2}(m + n)%N (leqnn (m + n)) => k; elim: k n m => [n m|k ihk n m hnm].
  by rewrite leqn0 addn_eq0; case/andP => /eqP -> /eqP ->; rewrite !binz0.
case: m hnm => [ | m] hnm //; case: n hnm => [ | n] hnm.
  rewrite bin_1N_posz {}ihk // !addr0 !binz_on_diag /= !mulr1.
  by rewrite exprSz mulN1r.
rewrite bin_negz_posz ihk; last by move: hnm; rewrite addnS.
rewrite ihk; last by move: hnm; rewrite addSn.
rewrite exprSzr -!mulrA !mulN1r -mulrBr; congr (_ * _); rewrite -opprD.
rewrite -!PoszD ![(m.+1 + _)%N]addSn [(_ + n.+1)%N]addnS -[(m + n).+2]addn1.
by rewrite -[m.+1]addn1 !PoszD Pascal_z.
Qed.

(* First, three weak versions of the recurrences verified by binomialz, *)
(* on a half plane only.*)
Lemma binzSS_weak (n k : int) : n >= 0 -> k + 1 != 0 ->
  binomialz (n + 1) (k + 1) = (n%:~R + 1) / (k%:~R + 1) * binomialz n k.
Proof.
move=> hn hk; case: (lerP k (-1 - 1)) => hk1.
  rewrite binz_neg; last by rewrite -ler_subr_addr.
  rewrite binz_neg; last by apply: le_trans hk1 _.
  by rewrite mulr0.
have {hk hk1}: k >= 0 by goal_to_lia; intlia.
case: n hn => n //; case: k => k // _ _.
rewrite mulrAC; apply/eqP. 
have -> m : Posz m + 1 = Posz m.+1 by rewrite -addn1 PoszD.
have h m : (Posz m)%:~R + 1 = (Posz m.+1)%:~R.
  by rewrite -[X in _ + X]/(Posz 1)%:~R -rmorphD -PoszD addn1.
rewrite !{}h eq_sym (can2_eq (divfK _) (mulfK _)) ?pnatr_eq0 //; apply/eqP.
rewrite !binz_nat_nat -!rmorphM /= -!PoszM.
by rewrite [(_ * _.+1)%N]mulnC addn1 mul_bin_diag.
Qed.

Lemma binzS_weak (n k : int) : n >= 0 -> k + 1 != 0 ->
  binomialz n (k + 1) = (n%:~R - k%:~R) / (k%:~R + 1) * binomialz n k.
Proof.
move=> hn hk; case: (lerP k (-1 - 1)) => hk1.
  rewrite binz_neg; last by rewrite -ler_subr_addr.
  rewrite binz_neg; last by apply: le_trans hk1 _.
  by rewrite mulr0.
have {hk1 hk}: k >= 0 by goal_to_lia; intlia.
case: n hn => n //; case: k => k // hn hk.
have -> : n%:~R - k%:~R = (n%:~R + 1) - (k%:~R + 1) :> rat.
  rat_field.
rewrite -mulrA mulrBl !mulrA -binzSS_weak //; last  by goal_to_lia; intlia.
rewrite divff ?mul1r; last first.
  by rewrite -[1]/(1%:~R) -rmorphD -PoszD pnatr_eq0 addn1.
by apply/eqP; rewrite eq_sym subr_eq; apply/eqP; rewrite Pascal_z.
Qed.


(* Now the most general versions of the previous three recurrences, assuming *)
(* only the non nullity of the denominator. *)

Lemma binzSS (n k : int) : k + 1 != 0 ->
binomialz (n + 1) (k + 1) = (n%:~R + 1) / (k%:~R + 1) * binomialz n k.
Proof.
case: (lerP 0 n); first exact: binzSS_weak.
case: (lerP k (-1 - 1)) => hkN2.
  rewrite binz_neg; last by rewrite -ler_subr_addr.
  rewrite binz_neg; last by apply: le_trans hkN2 _.
  by rewrite mulr0.
move=> hn hk1.
have {hkN2} hk : k >= 0 by goal_to_lia; intlia.
rewrite [LHS]binNzz [in RHS]binNzz.
have -> : k + 1 - (n + 1) - 1 = k - n - 1.
  by rewrite -![in LHS]addrA [1 + (_ + - 1)]addrCA subrr addr0 opprD addrA.
rewrite binzS_weak //; last by goal_to_lia; intlia.
rewrite !rmorphD !rmorphN /=; case: k hk1 hk => [k hk0 hk| //].
rewrite -[Posz k + 1]PoszD addn1 exprSzr.
set b := binomialz _ _; set c := (- 1) ^ k.
by rat_field; goal_to_lia; intlia.
Qed.

Lemma binzS (n k : int) : k + 1 != 0 ->
  binomialz n (k + 1) = (n%:~R - k%:~R) / (k%:~R + 1) * binomialz n k.
Proof.
move=> hk; case: (lerP k (-1 - 1)) => hk1.
  rewrite binz_neg; last by rewrite -ler_subr_addr.
  rewrite binz_neg; last by apply: le_trans hk1 _.
  by rewrite mulr0.
have -> : n%:~R - k%:~R = (n%:~R + 1) - (k%:~R + 1) :> rat.
  rat_field.
rewrite -mulrA mulrBl !mulrA -binzSS // divff ?mul1r; last first.
  by rewrite -[1]/(1%:~R) -rmorphD /= intr_eq0.
by apply/eqP; rewrite eq_sym subr_eq; apply/eqP; rewrite Pascal_z.
Qed.

Lemma binSz (n k : int): (k != n + 1) ->
  binomialz (n + 1) k = (n%:~R + 1) / (n%:~R + 1 - k%:~R) * binomialz n k.
Proof.
move=> hkn; case: (altP (k =P 0)) hkn => [-> | hk0] hkn.
  by rewrite !binz0 subr0 divff // -[1]/(1%:~R) -intrD intr_eq0 eq_sym.
have hk : k = (k - 1) + 1 by rewrite -addrA subrr addr0.
rewrite hk binzSS; last by rewrite -hk.
rewrite binzS; last by rewrite -hk.
rewrite !rmorphD !rmorphN /=; rat_field.
move: hk0 hkn hk; goal_to_lia; intlia.
Qed.

Lemma binz_gt0 (n k : int) :
  n >= 0 -> k >= 0 -> n >= k -> binomialz n k > 0.
Proof.
case: n => // n; case: k => // k _ _ lekn.
by rewrite binz_nat_nat -[0]/(intr 0) ltr_int ltz_nat bin_gt0.
Qed.

(* Below, older results, possibly needing revision. *)
Lemma binz_Znat_gt0 (n k : int) :
  n \is a Znat -> k \is a Znat -> n >= k -> binomialz n k > 0.
Proof.
case/ZnatP=> n1 ->; case/ZnatP=> k1 -> {n k} le_kn.
by rewrite binz_nat_nat -[0]/(intr 0) ltr_int ltz_nat bin_gt0.
Qed.

Lemma binznSn (n : int) : n \is a Znat -> binomialz n (n + 1) = 0.
Proof. by case/ZnatP => ? ->; rewrite -PoszD binz_nat_nat bin_small ?addn1. Qed.


(* was usksn in Section3 *)

Lemma binz_geq (n k : int) : n >= 0 -> k > n -> binomialz n k = 0.
Proof.
case: n => // n nge0 ltnk.
case: k ltnk => // k ltnk.
elim: n ltnk nge0 => [ltnk _ | n HIn ltSnk lt0Sn].
  by rewrite ltz_nat lt0n in ltnk; rewrite binz_nat_nat bin0n (negPf ltnk).
rewrite -addn1 PoszD binSz ?HIn ?mulr0 //.
  by rewrite ltz_nat ltnW.
by rewrite neq_lt -PoszD addn1 ltSnk orbT.
Qed.


(* was binzSn *)
(* same for that one : type cast or hypothesis on n? *)
Lemma binzSn (n : nat) (m : int) :
  binomialz (Posz n + 1) m =
  if m == Posz n + 1 then 1
  else ((Posz n)%:~R + 1) / ((Posz n)%:~R + 1 - m%:~R) * binomialz (Posz n) m.
Proof.
case: ifP => [ | hnm]; first by move/eqP->; rewrite binz_on_diag.
by apply: binSz; rewrite ?hnm.
Qed.

Lemma bin_nonneg (a b : int) : a >= 0 -> b >= 0 -> a >= b -> binomialz a b > 0.
Proof.
case: a => // n _.
case: b => // k _.
exact: binz_gt0.
Qed.

Lemma bin_int (a b : int) : a >= 0 -> b >= 0 ->
  exists e : nat, binomialz a b = (Posz e)%:~R.
Proof.
case: a => // n _.
case: b => // k _.
rewrite binz_nat_nat.
by exists 'C(n, k).
Qed.

Lemma bin_nonneg_int (a b : int) : a >= 0 -> b >= 0 -> a >= b ->
  exists e : int, binomialz a b = e%:~R /\ e > 0.
Proof.
move=> ha hb hab.
set m := binomialz a b.
have : m > 0 by apply: bin_nonneg; intlia.
have : exists n : nat, m = (Posz n)%:~R by apply: bin_int; intlia.
case=> n m_is_n.
have {m_is_n} n_is_m : n%:~R = m by rewrite m_is_n.
rewrite -n_is_m.
set j := Posz n => pos_j.
exists j.
split => //.
have : j <> 0.
  rewrite /not => j_eq_0.
  move: pos_j.
  by rewrite j_eq_0.
move=> {pos_j} j_neq_0.
have : j >= 0 by rewrite /j.
move=> nonneg_j.
intlia.
Qed.


(* Characterization of the zero values of binomialz *)

Lemma binz_eq0 (n k : int) :
  (binomialz n k == 0) = ((k < 0) || ((n >= 0) && (k > n))).
Proof.
apply/idP/idP=> h.
case: (ltrP k 0) => //= hk.
- case: (lerP 0 n) => /= hn.
    apply: contraLR h; rewrite -leNgt; move/(bin_nonneg hn hk).
    by rewrite lt0r; case/andP.
  apply: contraLR h => _.
  rewrite binNzz; apply: mulf_neq0; first by rewrite expfz_eq0 andbF.
  suff: binomialz (k - n - 1) k > 0 by rewrite lt0r; case/andP.
  have hnk : k <= k - n - 1 by goal_to_lia; intlia.
  by apply: bin_nonneg => //; apply: le_trans hnk.
case/orP: h => [h | /andP [h1 h2]]; apply/eqP; first by apply: binz_neg; intlia.
exact: binz_geq.
Qed.

(* This should be valid for any n and m, or better, vanish because binomialz *)
(* is changed to have its return value in int. *)
Lemma Qint_binomialz n m : n >= 0 -> m >= 0 -> binomialz n m \is a Qint.
Proof.
move=> le0n; case/(bin_int le0n) => i ->; exact: rpred_int.
Qed.

(************* Experimental, old, unsed stuff below this ************)

(* Experiments around the falling factorial function *)
Fixpoint ffact_rec (n : int) (m : nat) :=
  if m is m'.+1 then n * ffact_rec (n - 1) m' else 1.

Definition falling_factorial := nosimpl ffact_rec.

Notation "n ^_ m" := (falling_factorial n m)
  (at level 30, right associativity) : nat_scope.

Fact ffactE : falling_factorial = ffact_rec. Proof. by []. Qed.

Fact ffactn0 (n : int) : n ^_ 0 = 1. Proof. by []. Qed.

Fact ffact0n (m : nat) : 0 ^_ m = (m == 0%N).
Proof.
by case: m => // [] [ | n] //; rewrite /falling_factorial /ffact_rec mul0r.
Qed.

Fact ffactnS (n : int) (m : nat) : n ^_ m.+1 = n * (n - 1) ^_ m.
Proof.  by [].  Qed.

Fact ffactn1 (n : int) : n ^_ 1 = n. Proof. exact: mulr1. Qed.

Lemma ffactnSr (n : int) (m : nat) : n ^_ m.+1 = n ^_ m * (n - Posz m).
Proof.
elim : m n => [ | m Hm] n.
  by rewrite ffactn1 ffactn0 mul1r subr0.
rewrite ffactnS Hm ffactnS -mulrA; repeat congr (_ * _).
by rewrite -!addrA; congr(_ + _); rewrite -addn1 -oppz_add addrC.
Qed.

(* Do not know yet if signed conditions are better expressed as such or as
 \is a Znat conditions *)
Lemma ffact_gt0 (n : int) (m : nat) : n >= 0 -> (0 < n ^_ m) = (Posz m <= n).
Proof.
case: n => // n _; elim: n m => [ | n IHn] [ | m] //=.
  by rewrite ffact0n /= lez0_nat.
by rewrite ffactnS subzSS subr0 pmulr_rgt0 // IHn.
Qed.

Lemma ffact_ge0 (n : int) (m : nat) : n >= 0 -> 0 <= n ^_ m.
Proof.
case: n => n //.
elim: n m => [ | n ihn] m _; first by rewrite ffact0n.
case: m ihn => [ | m] ihn; first by rewrite ffactn0.
by rewrite ffactnS subzSS subr0 pmulr_rge0 // ihn.
Qed.

Lemma ffact_small (n m : nat) : Posz n < Posz m -> n ^_ m = 0.
Proof.
move=> hnm; apply/eqP; rewrite eq_le ffact_ge0 // leNgt ffact_gt0 //.
by rewrite -ltNge andbT.
Qed.

Lemma ffactnn (n : nat) : (Posz n) ^_ n = Posz n`!.
Proof.
by elim : n => [ | n Hn] //; rewrite ffactnS factS subzn // subn1 Hn PoszM.
Qed.
