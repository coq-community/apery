From mathcomp Require Import all_ssreflect all_algebra.

Require Import arithmetics multinomial floor.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import field_tactics.
Require Import lia_tactics.
Require Import extra_mathcomp.

Import Order.TTheory GRing.Theory Num.Theory.

Section BinomialMissing.

Lemma ffact_le_expn : forall m p, (p ^_ m <= p ^ m)%N.
elim => [|m HIm] => p //.
  rewrite ffactnSr expnS mulnC.
  by rewrite leq_mul ?HIm // leq_subr.
Qed.

End BinomialMissing.

Section PrimeMissing.
Local Open Scope nat_scope.

Lemma lognn p (Hp : prime p) : logn p p = 1.
Proof.
by rewrite -(pfactorK 1 Hp).
Qed.

Lemma partp_dvdn p (Hprime : prime p) n m :
  (0 < n) -> (p ^ m %| n) -> p ^ m %| n`_p .
Proof.
move => Hn Hdiv; rewrite -(pfactorK m Hprime) -p_part.
by rewrite partn_dvd //.
Qed.

End PrimeMissing.

Section DefinitionOfA.

Local Open Scope nat_scope.

Fixpoint a (n : nat) : nat :=
  match n with
  | 0 => 2
  | k.+1 => ((a k) * ((a k).-1)).+1
  end.

Arguments a n : simpl never.
(* As usual, we start with  a 0 = 2 but with a 1 = 2 in the paper proof *)

(* Here are a few values of a, that will be used later in the majoration which is
   the crux of the proof. *)
Lemma a0 : a 0 = 2. Proof. by []. Qed.
Lemma a1 : a 1 = 3. Proof. by []. Qed.
Lemma a2 : a 2 = 7. Proof. by []. Qed.
Lemma a3 : a 3 = 43. Proof. by []. Qed.
Lemma a4 : a 4 = 1807. Proof. by []. Qed.

(* We start with trivial facts, tagged in order to feed automation tools in
   further proofs *)
Lemma aS (n : nat) : a (n.+1) = ((a n) * ((a n).-1)).+1.
Proof. by []. Qed.

Lemma a_pos n : 0 < a n.
Proof. by case: n => [| n]. Qed.
Hint Resolve a_pos.

Lemma a_gt1 n : 1 < a n.
Proof.
by elim: n => [| n ihn] //=; rewrite aS ltnS muln_gt0; case: (a n) ihn.
Qed.
Hint Resolve a_gt1.

Lemma pa_gt0 n : 0 < (a n).-1.
Proof. by rewrite -ltnS prednK. Qed.
Hint Resolve pa_gt0.

Lemma a_grows1 n : a n < a n.+1.
Proof. by rewrite /= ltnS leq_pmulr //; case: (a n) (a_gt1 n). Qed.

Lemma a_grows2 m n : a m < a (m + n.+1).
Proof.
elim: n => [| n ihn] /=; first by rewrite addn1 a_grows1.
by apply: ltn_trans ihn _; rewrite !addnS a_grows1.
Qed.

Lemma a_grows m n : m <= n -> a m <= a n.
Proof.
move/subnK<-; rewrite addnC; case: (n - m) => [| k]; first by rewrite addn0.
apply: ltnW; apply: a_grows2.
Qed.

Lemma aS_gt2 k : (2 < a k.+1)%nat.
Proof.
suff H1 : (2 < a 1)%nat => // .
apply (leq_trans H1).
apply: a_grows => // .
Qed.

Lemma a_rec (n : nat) : a n = \prod_(0 <= i < n) a i + 1.
Proof.
elim: n => [|n Hn] //=; first by rewrite big_nil.
by rewrite aS {2}Hn addn1 /= big_nat_recr //= mulnC addn1.
Qed.


(* A copy of a, inside the type rat of rational numbers, plus copies of the
   previous lemmas. This definition is here to lock a in rat : otherwise
   spurious simplification may be performed by /= and result in (_ * _)%:~R
   which is possibly bad for rat_field... The problem may be solved by
   making a simpl never. *)
Local Open Scope ring_scope.

Definition a_rat (n : nat) : rat := (a n)%:Q.

(* Unfortunately, we need to duplicate the trivialities, in order to make them
 available to the copies of a in rational numbers. *)
Lemma a_rat_gt1 (n : nat) : 1 < (a n)%:Q. Proof. by rewrite ltr1n. Qed.
Hint Resolve a_rat_gt1.

Lemma a_rat_sub1_gt0 (n : nat) : 0 < (a n)%:Q - 1. by rewrite subr_gt0. Qed.
Hint Resolve a_rat_sub1_gt0.

Lemma a_rat_pos (n : nat) : 0 < (a n)%:Q. Proof. by rewrite /a_rat ltr0n. Qed.
Hint Resolve a_rat_pos.

Lemma a_rat_ge0 (n : nat) : 0 <= (a n)%:Q. Proof. by rewrite /a_rat ler0n. Qed.
Hint Resolve a_rat_ge0.

Lemma a_rat_rec1 (n : nat) : (a (n.+1))%:Q = (a n)%:Q * ((a n)%:Q - 1) + 1.
Proof.
by rewrite aS -addn1 PoszD rmorphD /= PoszM rmorphM /= predn_int // rmorphB.
Qed.

(* NOT USED *)
Lemma a_rat_rec (n : nat): a_rat n = \prod_ (0 <= i < n) (a_rat i) + 1.
Proof.
by rewrite /= /a_rat a_rec PoszD rmorphD /= prodMz.
Qed.

End DefinitionOfA.

(* We lack a "Global" for Hint Resolve. *)
Hint Resolve a_pos.
Hint Resolve a_gt1.
Hint Resolve pa_gt0.

Hint Resolve a_rat_gt1.
Hint Resolve a_rat_sub1_gt0.
Hint Resolve a_rat_pos.
Hint Resolve a_rat_ge0.

Section BoundsOnA.

Local Open Scope nat_scope.

Lemma a_lower_bound (k : nat) :  2 ^ (2 ^ k).+1 < a k.+2.
Proof.
elim: k => [| k ihk] //.
rewrite aS ltnS.
have -> : 2 ^ (2 ^ k.+1).+1 = 2 ^ (2 ^ k).+1 * 2 ^ (2 ^ k).
  by rewrite -expnD addSn addnn -mul2n -expnS.
  apply: leq_mul; first exact: ltnW.
by rewrite -ltnS prednK //; apply: ltn_trans ihk; rewrite ltn_exp2l.
Qed.

(* (* In fact we only need this less tight bound: *) *)
Lemma a_lower_boundW (k : nat) : 2 ^ 2 ^ k <= a k.+2.
Proof.
by apply: ltnW; apply: ltn_trans (a_lower_bound _); rewrite ltn_exp2l.
Qed.


(* (* In the paper, the hypothesis is  a k.+2 <= n < a k.+3.*) *)
Lemma hanson_5 (k n : nat) :
   a k.+2 <= n -> k <= trunc_log 2 (trunc_log 2 n).
Proof.
move=> leaSSn; do 2! (apply: trunc_log_max => //); apply: leq_trans leaSSn.
exact: a_lower_boundW.
Qed.

Lemma k_bound n k (Hank : (a k <= n < (a k.+1))%nat) (le2k : (k >= 2)%nat) :
  (k <= trunc_log 2 (trunc_log 2 n) + 2)%nat.
Proof.
case/andP: Hank => lean lena.
case: k lean lena le2k => // k lean lena le2k.
case: k lean lena le2k => // k lean lena le2k.
rewrite -addn1 -addn1 -addnA addn1.
rewrite leq_add // . exact: hanson_5.
Qed.

Lemma Observation_compare_a_a i : (a i).-1 ^ 2 < a (i.+1) < (a i) ^ 2.
Proof.
rewrite aS ltnS -!mulnn leq_pmul2r // leq_pred /= -addn1 addSn.
have -> : a i * a i = a i * (a i).-1 + a i by rewrite -mulnSr prednK.
by rewrite ltn_add2l.
Qed.

(* Function returning the unique k such that a k <= n < a k.+1 *)
Fixpoint f_k (n : nat) :=
  match n with
    | 0 => 0
    | n.+1 => let k0 := f_k n in
              if n.+1 < a k0.+1 then k0 else k0.+1
  end.

Lemma n_between_a n (Hn : (2 <= n)) :
  (a (f_k n) <= n < a ((f_k n).+1)).
Proof.
elim: n Hn => // n; set k0 := f_k n => ihn.
rewrite leq_eqVlt; case/orP; first by move/eqP <-.
have -> : f_k n.+1 = if n.+1 < a k0.+1 then k0 else k0.+1 by [].
rewrite ltnS; move/ihn.
case: ifP; first by move -> => /andP [Hn _]; rewrite ltnW.
move => Hf /andP [H1 H2].
by rewrite leq_eqVlt Hf orbF in H2; move /eqP: H2 => ->; rewrite a_grows1 leqnn.
Qed.

End BoundsOnA.

(* An important property of the sequence (a i) is that the sum of its inverses
   is less than 1. For this we need a different scope, for rational numbers. *)

Section MajorationOfTheSumOfInversesOfA.

Local Open Scope ring_scope.

Lemma sum_aV (n : nat) :
  \sum_(0 <= i < n.+1) (a i)%:Q ^-1 = ((a n.+1)%:Q - 2%:Q) / ((a n.+1)%:Q - 1).
Proof.
elim: n => [|n ihn]; first by rewrite big_mkord big_ord1.
pose an1 := (a n.+1)%:Q; pose an2 := (a n.+2)%:Q.
suff step : (an1 - 2%:~R) / (an1 - 1) + an1 ^-1 = (an2 - 2%:~R) / (an2 - 1).
  by rewrite big_nat_recr // ihn /= step.
have -> : an2 = an1 * (an1 - 1) + 1 by exact: a_rat_rec1.
have for_field1 : an1 - 1 <> 0 by move/eqP; apply/negP; rewrite /an1 lt0r_neq0.
have for_field2 : an1 <> 0 by move/eqP; apply/negP; rewrite eq_sym /an1 ltr_neq.
have for_field3 : ((an1 * (an1 - 1)) + 1) - 1 <> 0.
  by move/eqP; apply/negP; rewrite addrK mulf_neq0 => //; apply/negP; move/eqP.
rat_field.
done.
Qed.


Corollary lt_sum_aV_1 (n : nat) : \sum_(0 <= i < n.+1) (a i)%:Q ^-1 < 1.
Proof. by rewrite sum_aV ltr_pdivr_mulr // mul1r ltr_add2l. Qed.


(* NOT USED? *)
(* observation in lemma 5 from original Hanson paper *)
Corollary sum_aV_bis (n : nat) :
  \sum_(0 <= i < n.+1) ((a i).-1)%:Q / (a_rat i) =
   n.+1%:R - (a_rat n.+1 - 2%:~R) / (a_rat n.+1 - 1).
Proof.
have -> : \sum_(0 <= i < n.+1) ((a i).-1)%:Q / a_rat i =
          \sum_(0 <= i < n.+1) (1 - (a_rat i) ^-1).
  apply: eq_bigr => i _; rewrite -subn1 -subzn ?a_pos // ?rmorphB /= .
  rewrite /a_rat // ; rat_field. rewrite /emb.
  have -> : 0%Q = 0%:~R by []; rewrite eqr_int_prop.
  have Hpos := (a_pos i); rewrite -ltz_nat in Hpos.
  by move => Habs; rewrite Habs in Hpos.
by rewrite sumrB big_mkord sumr_const /= card_ord sum_aV.
Qed.


(* Now the corollaries in terms of Euclidean quotients. *)
Local Open Scope nat_scope.

Corollary suminv_lt1 i n : 0 < n ->  \sum_(0 <= j < i) n %/ a j < n.
Proof.
case: n => [| n] // _; case: i => [| i]; first by rewrite big_nil.
suff : (((\sum_(0 <= j < i.+1) n.+1 %/ a j)%N)%:Q < n.+1%:Q)%R.
  by rewrite -ltz_nat ltr_int.
suff hdiv : (\sum_(0 <= i0 < i.+1) (n.+1%:Q / (a i0)%:Q) < n.+1%:Q)%R.
  apply: le_lt_trans hdiv; rewrite sumMz; apply: ler_sum => j _.
  rewrite ler_pdivl_mulr // -intrM ler_int; exact: leq_trunc_div.
rewrite -mulr_sumr gtr_pmulr; last exact: ltr0z.
exact: lt_sum_aV_1.
Qed.

Corollary sum_aV_leqn n k : \sum_(0 <= i < k) n %/ a i <= n.
Proof.
case: n => [|n]; first by rewrite big1 // => i _; exact: div0n.
case: k => [| k]; first by rewrite big_nil.
apply: ltnW; exact: suminv_lt1.
Qed.


End MajorationOfTheSumOfInversesOfA.


(* Here is the sequence C(n) we will be studying throughout the proof. Note
  that we use an alternative definition as a multinomial coefficient, in order
  to make it an integer 'by construction'. In both versions of the definition,
   we need to make sense of a casual use of dots ... *)

Section DefinitionOfCandValuations.

Local Open Scope nat_scope.

(* Note that the formal definition and notations of multinomials is still a
   bit rough... *)
Definition C_row n k :=
  rcons (mkseq (fun i => n %/ (a i)) k) (n - (\sum_(0 <= i < k) n %/ a i)).

Definition C n k : nat := 'C[C_row n k] * (n - \sum_(0 <= i < k) n %/ a i)`!.

Lemma C_pos n k : 0 < C n k.
  by rewrite muln_gt0 multi_gt0 fact_gt0.
Qed.
Hint Resolve C_pos.

Lemma nth_C_row n k i :
  nth 0 (C_row n k) i =
  if i < k then n %/ a i
  else if i == k then (n - (\sum_(0 <= i < k) n %/ a i))
  else 0.
Proof.
by rewrite /C_row nth_rcons size_mkseq; case: ifP=> // ltik; rewrite nth_mkseq.
Qed.

Lemma size_C_row n k : size (C_row n k) = k.+1.
Proof. by rewrite /C_row size_rcons size_mkseq. Qed.

(* We prove that C(n) > lcm(1 ... n) by comparing their p-valuations. *)

Definition beta (p n k : nat) := logn p (C n k).

Lemma C_multi n k : \prod_(0 <= i < k) (n %/ a i)`! * C n k = n`!.
Proof.
rewrite /C -mulnCA; set l := C_row n k; set p := (X in _ * X = _).
suff [-> ->] : n = (\sum_(0 <= i < size l) nth 0 l i) /\
               p = \prod_(0 <= i < size l) (nth 0 l i)`! by exact: eq_def_multi1.
have nth_l i : 0 <= i < k -> (n %/ a i) = nth 0 (C_row n k) i.
  by case/andP => [_ ltik]; rewrite nth_C_row ltik.
have {p} -> : p = \prod_(0 <= i < size l) (nth 0 l i)`!.
  rewrite /l size_C_row big_nat_recr //= nth_C_row ltnn eqxx; congr (_ * _).
  by apply: eq_big_nat => ? ?; rewrite nth_l.
suff -> : n = \sum_(0 <= i < size l) nth 0 l i by [].
rewrite /l size_C_row big_nat_recr //= nth_C_row ltnn eqxx.
have -> : \sum_(0 <= i < k) nth 0 (C_row n k) i = \sum_(0 <= i < k) n %/ a i.
  by apply: eq_big_nat => ? ?; rewrite nth_l.
rewrite subnKC //; exact: sum_aV_leqn.
Qed.

Lemma C_0k k : C 0 k = 1.
Proof.
move: (C_multi 0 k).
have -> : \prod_(0 <= i < k) (0 %/ a i)`! = 1.
  by apply: big1 => i _; rewrite div0n fact0.
by rewrite mul1n fact0.
Qed.

(* The p valuation of a natural number k is (logn p k). So here is a formula
   for the p-valuation of (C n k) *)
Lemma betaE p n k : prime p ->
  beta p n k = logn p (n`!) - logn p ((\prod_(0 <= i < k) ((n %/ a i)`!))).
Proof.
move => Hprime; rewrite -(logn_div p); last first.
  by rewrite -(C_multi n k) dvdn_mulr.
by rewrite -(C_multi n k) mulKn //; apply: prodn_gt0=> i; apply: fact_gt0.
Qed.


(* This is Lemma 2 in Hanson's paper *)
Lemma Hanson_2 (p n k : nat) : prime p ->  trunc_log p n <= beta p n k.
Proof.
move => Hprime; case: (posnP n) => [-> | posn]; first by rewrite trunc_logn0.
rewrite betaE // logp_sum_floor // logn_prod; last by move=> i; exact: fact_gt0.
have -> : \sum_(0 <= i < k) logn p (n %/ a i)`! =
          \sum_(0 <= i < k) \sum_(j < trunc_log p n) (n %/ a i) %/ p ^ j.+1.
  apply: eq_bigr => i _; apply: fact_logp_sum_small => //.
  exact/leq_ltn_trans/trunc_log_ltn/prime_gt1/Hprime/leq_div.
have -> :
  \sum_(0 <= i < k) \sum_(j < trunc_log p n) (n %/ a i) %/ p ^ j.+1 =
  \sum_(j < trunc_log p n) \sum_(0 <= i < k)  (n %/ a i) %/ p ^ j.+1.
  exact: exchange_big_dep.
suff maj j : j < trunc_log p n ->
             \sum_(0 <= i < k) (n %/ a i) %/ p ^ j.+1 < n %/ p ^ j.+1.
  rewrite natsumrB; last by case=> i hi _ /=; apply: ltnW; apply: maj.
  have {1}-> : trunc_log p n = \sum_(j < trunc_log p n) 1 by rewrite sum1_ord.
  by apply: leq_sum=> [] [i hi] _; rewrite subn_gt0; apply: maj.
have {Hprime} lt1p : 1 < p by exact: prime_gt1.
rewrite -(leq_exp2l j.+1 _ lt1p) => hj.
have {hj} hj : p ^ j.+1 <= n by apply: leq_trans hj _; apply: trunc_logP.
have -> : \sum_(0 <= i < k) (n %/ a i) %/ p ^ j.+1 =
          \sum_(0 <= i < k) (n %/ p ^ j.+1) %/ a i.
  by apply: eq_bigr=> i; rewrite divnAC.
by apply: suminv_lt1; rewrite divn_gt0 // expn_gt0 (ltn_trans _ lt1p).
Qed.

Lemma part_p_iter_lcmn p (Hprime : prime p) n :
  {j : nat | (j <= n) && ((iter_lcmn n)`_p == j`_p)}.
Proof.
elim: n => [|n ihn].
  by exists 0; rewrite leqnn iter_lcmn0 partn0 partn1.
case: ihn => j /andP [lejn] /eqP ihn.
have H1 m : (iter_lcmn m)`_p = \big[lcmn/1%N]_(1 <= i < m.+1) i`_p.
  by rewrite /iter_lcmn !big_add1 /= 2!big_mkord partn_biglcm.
have {H1} H2 : (iter_lcmn n.+1)`_p = lcmn j`_p n.+1`_p.
  rewrite H1 big_add1 big_nat_recr // -ihn /=; congr lcmn.
  by rewrite H1 big_add1 /= .
have {H2}-> : (iter_lcmn n.+1)`_p =
              if logn p j < logn p n.+1 then n.+1`_p else j`_p.
  by rewrite H2 2!p_part -expn_max /maxn; case: ifP.
case  : ifP.
  by exists n.+1; rewrite ltnS leqnn eq_refl.
by exists j; rewrite (leqW lejn) eq_refl.
Qed.

Lemma part_p_iter_lcmn_trunc_log p (Hprime : prime p) n :
  (iter_lcmn n)`_p = p ^ trunc_log p n.
Proof.
wlog: / 0 < n => [|n_gt0].
  move => Hn.
  case: n Hn => // [|n ihn].
    move => _; by rewrite iter_lcmn0 partn1 trunc_logn0 expn0.
  exact :ihn.
have p_gt1 : 1 < p by exact: prime_gt1.
have p_gt0 : 0 < p by exact: prime_gt0.
suff H2ineq :  (iter_lcmn n)`_p <= p ^ trunc_log p n /\
               p ^ trunc_log p n <= (iter_lcmn n)`_p.
apply: anti_leq; apply/andP; split; by case: H2ineq.
split.
- case: (part_p_iter_lcmn Hprime n) => j /andP [lejn /eqP lcmnpj].
  case: j lejn lcmnpj => [|j] lejn lcmnpj.
    by rewrite lcmnpj partn0 expn_gt0 p_gt0.
  rewrite lcmnpj p_part.
  exact/leq_pexp2l/leq_logn_trunc.
- apply/dvdn_leq/partp_dvdn/iter_lcmn_div/trunc_logP => //.
  by rewrite expn_gt0 p_gt0.
Qed.

Lemma lcm_leq_Cnk n k : iter_lcmn n <= C n k.
Proof.
case: n => [|n]; first by rewrite iter_lcmn0 .
set ln := iter_lcmn n.+1.
suff Hdiv : ln %| C n.+1 k.
  exact: dvdn_leq => // .
apply/dvdn_partP => [|p Hp]; first by (rewrite iter_lcmn_gt0).
have Hprime : prime p by move: Hp; rewrite mem_primes; case/andP.
suff Hlogntrunc: logn p ln <= logn p (C n.+1 k).
  by rewrite p_part pfactor_dvdn.
suff lelogtrunc : logn p ln <= trunc_log p n.+1.
  exact: leq_trans (Hanson_2 _ _ _).
apply: trunc_log_max; first by rewrite prime_gt1.
suff Hj : {j | (j <= n.+1) && (ln`_p == j`_p)}.
  case: Hj => j /andP [Hj1 Hj2]; rewrite -p_part; move/eqP: Hj2 => -> .
  case: j Hj1 => [|j Hj1]; first by rewrite partn0.
  exact/leq_trans/Hj1/dvdn_leq/dvdn_part.
exact: part_p_iter_lcmn.
Qed.

End DefinitionOfCandValuations.

(* This section presents a first bound on C(n,k) *)
Section BoundOnC.

Local Open Scope nat_scope.

(* Lemma 8 of "Hanson Summary" paper *)
Lemma l8 n k :
  (\prod_(0 <= i < k) (n %/ a i) ^ (n %/ a i)) * C n k <= n ^ n.
Proof.
pose t := \sum_(0 <= i < k) (n %/ a i).
have letn : t <= n by exact: sum_aV_leqn.
suff step1 :
  \prod_(0 <= i < k) (n %/ a i) ^ (n %/ a i) * C n k <= n ^ (n - t) * t ^ t.
  apply: leq_trans step1 _; case: n t letn => [t | n t leqnSt].
  - by rewrite leqn0 => /eqP->.
  have e : n.+1 = n.+1 - t + t by rewrite subnK.
  rewrite [in X in _ <= _ ^ X]e {e} expnD leq_mul2l.
  case: t leqnSt => [| t] leqnSt; first by rewrite !expn0 orbT.
  by rewrite leq_exp2r // leqnSt orbT.
  pose l := mkseq (fun i : nat => n %/ a i) k.
  have lP : 'C[l] * \prod_(0 <= i < k) (n %/ a i) `! = t `!.
     have -> : \prod_(0 <= i < k) (n %/ a i)`! = \prod_( j <- l) j `! .
       rewrite [in RHS](big_nth 0) size_mkseq big_nat_cond [RHS]big_nat_cond.
       apply: eq_bigr => i /andP [/andP [le0i ltik] _].
       by rewrite nth_mkseq //.
     have -> : t = \sum_(j <- l) j.
       rewrite /t [RHS](big_nth 0) size_mkseq big_nat_cond [RHS]big_nat_cond.
       apply: eq_bigr => i /andP [/andP [le0i ltik] _] .
       by rewrite nth_mkseq // .
     exact: multi_prod_fact.
  have /eqP -> : C n k == (n ^_ (n - t)) * 'C[l].
    have /eqn_pmul2l <- : \prod_(0 <= i < k) (n %/ a i) `! > 0.
      by apply: prodn_gt0 => i; rewrite fact_gt0.
    rewrite C_multi mulnA mulnC mulnA lP mulnC.
    have {2}-> : t = n - (n - t) by rewrite subKn.
    by rewrite ffact_fact // leq_subr.
have -> : \prod_(0 <= i < k) (n %/ a i) ^ (n %/ a i) = \prod_( j <- l) j ^ j.
  rewrite [in RHS](big_nth 0) size_mkseq big_nat_cond [RHS]big_nat_cond.
  apply: eq_bigr => i /andP [/andP [le0i ltik] _].
  by rewrite nth_mkseq //.
have Ht : t = \sum_(i <- l) i.
  rewrite /t [in RHS](big_nth 0) size_mkseq big_nat_cond [RHS]big_nat_cond.
  apply: eq_bigr => i /andP [/andP [le0i ltik] _].
  by rewrite nth_mkseq //.
rewrite mulnC -mulnA.
apply: leq_mul.
- exact: ffact_le_expn.
- by rewrite Ht; apply: multinomial_ineq.
Qed.

End BoundOnC.

Section UsefulBound.

Local Open Scope nat_scope.

(* nat equivalent of 1 + x <= exp x *)
Lemma replace_exponential (n : nat) : 1 + n <= 3^n.
Proof.
elim: n => [|n HIn] // .
apply: (@leq_trans (1 + 3 ^ n)); first by rewrite leq_add2l.
by rewrite addnC expnS mulSn leq_add2l muln_gt0 expn_gt0.
Qed.

End UsefulBound.
