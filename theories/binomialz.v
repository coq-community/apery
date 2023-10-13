From mathcomp Require Import all_ssreflect all_algebra.
Require Import tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* A binomial function over signed integers*)
Fixpoint binomial_rec (n m : nat) (pn pm : bool) : int :=
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

Definition binomialz (n m : int) : int :=
match n,m with
| Posz n1, Posz m1 => binomial_rec n1 m1 true true
| Negz n1, Posz m1 => binomial_rec n1 m1 false true
| Posz n1, Negz m1 => binomial_rec n1 m1 true false
| Negz n1, Negz m1 => binomial_rec n1 m1 false false
end.

Arguments binomialz n m : simpl never.

(* Eval compute in binomialz 5 3.*)

(* Facts from the recursive code defining of binomialz. *)
Fact binz0 (n : int) : binomialz n 0 = 1.
Proof. by case: n => n. Qed.

Fact binz_neg (n m : int) : m <= -1 -> binomialz n m = 0.
Proof. by case: m => m //= _; case: n => n; case: m. Qed.

Fact bin0z (m : int) : 1 <= m -> binomialz 0 m = 0.
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
Lemma bin_1N (m : int) : 0 <= m -> binomialz (Negz 0) m = (- 1) ^ m.
Proof.
by case: m => + // _; elim=> // m ihm; rewrite bin_1N_posz ihm exprSz mulN1r.
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

Lemma binz_nat_nat (n m : nat) : binomialz (Posz n) (Posz m) = 'C(n, m).
Proof.
elim: n m => [ | n Hn] [ | n0] //.
rewrite -[in LHS](addn1 n) -[in LHS](addn1 n0) 2!PoszD Pascal_z binS.
by rewrite !Hn addn1 PoszD.
Qed.

Lemma binzE (F : numFieldType) (m n : nat) : (m <= n)%N ->
  (binomialz (Posz n) (Posz m))%:~R =
    (Posz n`!)%:~R / ((Posz m`!)%:~R * (Posz (n - m)`!)%:~R) :> F.
Proof.
move=> hmn; rewrite binz_nat_nat; apply/eqP.
rewrite -(bin_fact hmn) !PoszM !rmorphM mulfK //=.
by apply/mulf_neq0; rewrite pnatr_eq0 lt0n_neq0 ?fact_gt0.
Qed.

Lemma binzE_ffact (F : numFieldType) (m n : nat) :
  (binomialz (Posz n) (Posz m))%:~R = (Posz (n ^_ m))%:~R / (Posz m`!)%:~R :> F.
Proof.
apply/eqP; rewrite binz_nat_nat -bin_ffact !PoszM !rmorphM mulfK //=.
by rewrite pnatr_eq0 lt0n_neq0 ?fact_gt0.
Qed.

Lemma binz_on_diag (n : int) : binomialz n n = (0 <= n).
Proof.
case: n => n; last by rewrite binz_neg.
by rewrite binz_nat_nat binn.
Qed.

(* A property to transfer relations that are first proved on nonnegative *)
(* upper argument of the binomial. *)
Lemma binNzz (n m : int) : binomialz n m = (- 1) ^ m * binomialz (m - n - 1) m.
Proof.
wlog: m n / n <= 0.
  case: n => n; last exact.
  case: m => m; last by rewrite !binz_neg // mulr0.
  rewrite binz_nat_nat -addrA -opprB opprK.
  case: (ltnP n m) => hnm hwlog.
    by rewrite bin_small // subzn // binz_nat_nat bin_small ?mulr0; lia.
  have {}hnm : Posz m - Posz n.+1 <= 0 by rewrite subr_le0; apply/leqW/hnm.
  rewrite [in RHS]hwlog // subKr addrAC subrr add0r.
  by rewrite binz_nat_nat mulrA /exprz /= -exprMn mulrNN mul1r expr1n mul1r.
case: m => m; last by rewrite !binz_neg // mulr0.
case: n => [n | n _].
  case: n => [_ | //]; case:m => [ | m]; first by rewrite !binz0.
  by rewrite bin0z // subr0 subzSS subr0 binz_nat_nat bin_small // mulr0.
rewrite [in RHS]NegzE opprK -addrA subzSS subr0.
move: {2}(m + n)%N (leqnn (m + n)) => k; elim: k n m => [n m|k ihk n m hnm].
  by rewrite leqn0 addn_eq0; case/andP => /eqP -> /eqP ->; rewrite !binz0.
case: m hnm => [ | m] hnm //; case: n hnm => [ | n] hnm.
  by rewrite bin_1N_posz {}ihk // !addr0 !binz_on_diag /= !mulr1 exprSz mulN1r.
rewrite bin_negz_posz ihk; last by move: hnm; rewrite addnS.
rewrite ihk; last by move: hnm; rewrite addSn.
rewrite exprSzr -!mulrA !mulN1r -mulrBr; congr (_ * _); rewrite -opprD.
rewrite -!PoszD ![(m.+1 + _)%N]addSn [(_ + n.+1)%N]addnS -[(m + n).+2]addn1.
by rewrite -[m.+1]addn1 !PoszD Pascal_z.
Qed.

(* First, three weak versions of the recurrences verified by binomialz, *)
(* on a half plane only.*)
Lemma binzSS_weak (F : numFieldType) (n k : int) : 0 <= n -> k + 1 != 0 ->
  (binomialz (n + 1) (k + 1))%:~R =
    (n + 1)%:~R / (k + 1)%:~R * (binomialz n k)%:~R :> F.
Proof.
case: n k => [] // n [k|[|k]] // _ _; last by rewrite !binz_neg // mulr0.
rewrite -!PoszD !addn1 !binz_nat_nat mulrAC.
apply: canRL (mulfK _) _; rewrite ?intr_eq0 //.
by rewrite -!intrM -!PoszM mul_bin_diag mulnC.
Qed.

Lemma binzS_weak (F : numFieldType) (n k : int) : n >= 0 -> k + 1 != 0 ->
  (binomialz n (k + 1))%:~R =
    (n - k)%:~R / (k + 1)%:~R * (binomialz n k)%:~R :> F.
Proof.
case: n k => [] // n [k|[|k]] // _ _; last by rewrite !binz_neg // mulr0.
have ->: (Posz n - Posz k) = ((Posz n + 1) - (Posz k + 1)) by ring.
rewrite rmorphB !mulrBl /= -binzSS_weak //; last lia.
rewrite divff ?mul1r; last ring_lia.
by rewrite Pascal_z rmorphD addrK.
Qed.


(* Now the most general versions of the previous three recurrences, assuming *)
(* only the non nullity of the denominator. *)

Lemma binzSS (F : numFieldType) (n k : int) : k + 1 != 0 ->
  (binomialz (n + 1) (k + 1))%:~R =
    (n + 1)%:~R / (k + 1)%:~R * (binomialz n k)%:~R :> F.
Proof.
case: n => n; first exact: binzSS_weak.
case: k => [k|[|k]] // _; last by rewrite !binz_neg // !mulr0.
rewrite mulrAC; apply: (canRL (mulfK _)); first by ring_lia.
rewrite [LHS]mulrC [in LHS]binNzz [in RHS]binNzz !rmorphM /=.
rewrite opprD addrACA subrr addr0 mulrCA binzS_weak //; [|lia..].
by rewrite -PoszD addn1 exprSz; field; ring_lia.
Qed.

Lemma binzS (F : numFieldType) (n k : int) : k + 1 != 0 ->
  (binomialz n (k + 1))%:~R =
    (n - k)%:~R / (k + 1)%:~R * (binomialz n k)%:~R :> F.
Proof.
case: k => [k|[|k]] // _; last by rewrite !binz_neg // !mulr0.
have ->: n - Posz k = (n + 1) - (Posz k + 1) by ring.
rewrite rmorphB /= !mulrBl -binzSS; last lia.
rewrite divff; last ring_lia.
by rewrite mul1r Pascal_z rmorphD addrK.
Qed.

Lemma binSz (F : numFieldType) (n k : int) : (k != n + 1) ->
  (binomialz (n + 1) k)%:~R =
    (n + 1)%:~R / (n + 1 - k)%:~R * (binomialz n k)%:~R :> F.
Proof.
move=> hkn; case: (altP (k =P 0)) hkn => [-> | hk0] hkn.
  by rewrite !binz0 subr0 divff ?mul1r //; ring_lia.
have hk : k = k - 1 + 1 by rewrite -addrA subrr addr0.
rewrite hk binzSS; last by rewrite -hk.
rewrite binzS; last by rewrite -hk.
by field; ring_lia.
Qed.

Lemma binz_gt0 (n k : int) : 0 <= k -> k <= n -> 0 < binomialz n k.
Proof.
by case: n k => [] n [] k //= _ lekn; rewrite binz_nat_nat ltz_nat bin_gt0.
Qed.

(* Below, older results, possibly needing revision. *)
Lemma binz_Znat_gt0 (n k : int) :
  n \is a Znat -> k \is a Znat -> k <= n -> 0 < binomialz n k.
Proof. by move=> /ZnatP[{}n ->] /ZnatP[{}k ->] le_kn; rewrite binz_gt0. Qed.

Lemma binznSn (n : int) : n \is a Znat -> binomialz n (n + 1) = 0.
Proof. by case/ZnatP => ? ->; rewrite -PoszD binz_nat_nat bin_small ?addn1. Qed.


(* was usksn in Section3 *)

Lemma binz_geq (n k : int) : 0 <= n -> n < k -> binomialz n k = 0.
Proof.
by case: n k => [] // n [] // k _; rewrite binz_nat_nat => /bin_small ->.
Qed.

Lemma bin_nonneg (a b : int) : 0 <= b -> b <= a -> 0 < binomialz a b.
Proof. by case: a b => [] a [] b //= _; exact: binz_gt0. Qed.

Lemma bin_int (a b : int) :
  0 <= a -> 0 <= b -> exists e : nat, binomialz a b = Posz e.
Proof.
by case: a b => [] a [] b //= _ _; rewrite binz_nat_nat; exists 'C(a, b).
Qed.

Lemma bin_nonneg_int (a b : int) :
  0 <= b -> b <= a -> exists e : int, binomialz a b = e /\ e > 0.
Proof.
case: a b => [] a [] b //= _ leba.
by exists (Posz 'C(a, b)); rewrite binz_nat_nat [_ < _]bin_gt0.
Qed.


(* Characterization of the zero values of binomialz *)

Lemma binz_eq0 (n k : int) : (binomialz n k == 0) = (k < 0) || (0 <= n < k).
Proof.
apply/idP/idP=> h.
case: (ltrP k 0) => //= hk.
- case: (lerP 0 n) => /= hn.
    apply: contraLR h; rewrite -leNgt; move/(bin_nonneg hk).
    by rewrite lt0r; case/andP.
  apply: contraLR h => _.
  rewrite binNzz; apply: mulf_neq0; first by rewrite expfz_eq0 andbF.
  suff: 0 < binomialz (k - n - 1) k by rewrite lt0r; case/andP.
  have hnk : k <= k - n - 1 by lia.
  by apply: bin_nonneg => //; apply: le_trans hnk.
case/orP: h => [h | /andP [h1 h2]]; apply/eqP; first by apply: binz_neg.
exact: binz_geq.
Qed.

(************* Experimental, old, unsed stuff below this ************)

Module SignedFfact.

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
by rewrite -!addrA; congr(_ + _); rewrite -addn1 -oppzD addrC.
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

End SignedFfact.
