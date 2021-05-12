From mathcomp Require Import all_ssreflect all_algebra.
Require Import bigopz.
Require Import shift.

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.


(* Compare with (f ^~ y). *)
Let pfun2 Tx Ty Tz T (f : Tx -> Ty -> Tz -> T) z := (fun x y => f x y z).


Section CreativeTelescopingMasterLemma.

Variable R : ringType.

Fixpoint horner_seqop_rec (cf : seq (int -> R)) (u : int -> R) n n0 :=
  match cf with
  | [::] => 0
  | [:: a] => a n0 * u n
  | a :: cf' => horner_seqop_rec cf' u (int.shift 1%N n) n0 + a n0 * u n
  end.

Definition horner_seqop cf u n := horner_seqop_rec cf u n n.

Lemma horner_seqopP cf u n (cf0 := fun _ => 0) : horner_seqop cf u n =
  \sum_(0 <= i < size cf) nth cf0 cf i n * u (int.shift i n).
Proof.
rewrite /horner_seqop; elim: cf {1 4}n => [ | a cf' ihcf] m.
  by rewrite big_mkord big_ord0.
case: cf' ihcf => [_ /= | b cf' ihcf].
  by rewrite big_mkord big_ord1 /=.
have -> : horner_seqop_rec [:: a, b & cf'] u m n =
  (horner_seqop_rec [::b & cf'] u (int.shift 1%N m) n) + a n * u m by [].
symmetry; rewrite ihcf [size _]/= big_nat_recl // addrC; congr (_ + _).
apply: eq_bigr=> i _; congr (_ * _); rewrite !int.zshiftP -addn1 PoszD addrAC.
by rewrite addrA.
Qed.

Variable u : int -> int -> R.
Variable Pseq : seq (int -> R).
Variable Q : (int -> int -> R) -> (int -> int -> R).
Variables (a b : int).
Variable not_D : int -> int -> bool.

(* The intended use of sound_telescoping is by providing PeqDQ, all other
   arguments being implicit.  This will typically open a new goal
   for range_correct.  NB:
   - range_correct means that the range of summation for U has the right
     dependency in n for the formula in sound_telescoping to be expected
     (if a > n + b, the sum over i would have to be truncated below);
   - PeqDQ is the local relation determined by a computer-algebra computation,
     and needs to be written in terms of Pseq for U. *)
Lemma sound_telescoping
  (cf0 : int -> R := fun _ => 0)
  (r : nat := size Pseq)
  (P : (int -> R) -> int -> R := horner_seqop Pseq)
  (U : int -> R := fun n => \sum_(a <= k < n + b :> int) u n k)
  (n : int)
  (range_correct : a <= n + b)
  (PeqDQ :
    forall (n k : int), not_D n k ->
      P (u ^~ k) n = Q u n (int.shift 1 k) - Q u n k) :
P U n =
Q u n (n + b) - Q u n a +
\sum_(a <= k < n + b :> int | ~~ not_D n k)
  (P (u ^~ k) n - (Q u n (k + 1) - Q u n k)) +
\sum_(0 <= i < r)
  \sum_(0 <= j < i)
    nth cf0 Pseq i n * u (int.shift i n) (int.shift j (n + b)).
Proof.
pose cf_P := nth cf0 Pseq.
have step : P U n =
  \sum_(0 <= i < r)
    \sum_(a <= k < int.shift i n + b :> int)
      cf_P i n * u (int.shift i n) k.
  by rewrite /P horner_seqopP; apply: eq_bigr=> j _; rewrite /U mulr_sumr.
pose t1 :=
  \sum_(0 <= i < r)
    \sum_(a <= k < int.shift r n + b :> int)
      cf_P i n * u (int.shift i n) k.
pose t2 :=
  \sum_(0 <= i < r)
    \sum_(int.shift i n + b <= k < int.shift r n + b :> int)
      cf_P i n * u (int.shift i n) k.
have {step} step : P U n = t1 - t2.
  apply/eqP; rewrite eq_sym subr_eq; apply/eqP; rewrite {}step -big_split /=.
  rewrite [LHS]big_seq_cond [RHS]big_seq_cond; apply: eq_bigr=> i; simpl in i.
  rewrite andbT mem_index_iota; case/andP=> _ hi.
  rewrite -big_cat_int //= !int.shift2Z.
  - by apply: le_trans range_correct _; rewrite ler_add2r ler_addl.
  - by rewrite ler_add2r ler_add2l ltW.
have t1_step :
  t1 =
    \sum_(a <= k < int.shift r n + b :> int)
      \sum_(0 <= i < r)
        cf_P i n * u (int.shift i n) k.
  by rewrite /t1 [in LHS]exchange_big.
pose t11 :=
  \sum_(a <= k < n + b :> int)
    \sum_(0 <= i < r)
      cf_P i n * u (int.shift i n) k.
have t11_step :
  t11 =
    \sum_(a <= k < n + b :> int | not_D n k)
      (Q u n (int.shift 1 k) - Q u n k) +
    \sum_(a <= k < n + b :> int | ~~ not_D n k)
      \sum_(0 <= i < r)
        cf_P i n * u (int.shift i n) k.
  rewrite /t11.
  rewrite (bigID (fun k => not_D n k)) /=; congr (_ + _).
  rewrite [LHS]big_seq_cond [RHS]big_seq_cond; apply: eq_bigr=> i; simpl in i.
  by case/andP=> _ hi; rewrite -PeqDQ // /P horner_seqopP.
have {t11_step} t11_step :
  t11 =
    Q u n (n + b) - Q u n a -
    \sum_(a <= k < n + b :> int | ~~ not_D n k)
      (Q u n (int.shift 1 k) - Q u n k) +
    \sum_(a <= k < n + b :> int | ~~ not_D n k)
      \sum_(0 <= i < r)
        cf_P i n * u (int.shift i n) k.
  rewrite {}t11_step; congr (_ + _).
  rewrite -(telescopez (Q u n)) //.
  by rewrite [X in _ = X - _](bigID (fun k => not_D n k)) /= -addrA subrr addr0.
have {t1_step} t1_step :
  t1 = t11 +
    \sum_(n + b <= k < int.shift r n + b :> int)
      \sum_(0 <= i < r)
        cf_P i n * u (int.shift i n) k.
  by rewrite t1_step /t11 -big_cat_int // ler_add2r int.shift2Z cpr_add.
rewrite {}step {}t1_step {}t11_step.
rewrite -1![RHS]addrA -3![LHS]addrA; congr (_ + _).
rewrite -sumrN [LHS]addrA -big_split /=; congr (_ + _).
  rewrite [n + b]addrC [LHS]big_seq_cond [RHS]big_seq_cond;
    apply: eq_bigr=> i _.
  by rewrite addrC /P horner_seqopP.
rewrite exchange_big /= -sumrN -big_split /=.
rewrite [LHS]big_seq_cond [RHS]big_seq_cond; apply: eq_bigr=> i /andP [].
rewrite mem_index_iota; case/andP=> _ hi _; rewrite !int.shift2Z.
have hl : n + b <= n + i + b by rewrite ler_add2r ler_addl.
have hr : n + i + b <= n + r + b by rewrite ler_add2r ler_add2l ltW.
rewrite (big_cat_int _ _ _ hl hr) {hl hr} addrK [n + i + b]addrAC big_addz2l /=.
rewrite eq_big_int_nat /=; apply: eq_bigr=> ? _.
by rewrite int.shift2Z [n + b + _]addrC.
Qed.

End CreativeTelescopingMasterLemma.



Section CreativeTelescopingBivariateMasterLemma.

Variable R : ringType.

Section BivHorner.

Variables (cf : seq (int -> int -> R)) (u : int -> int -> R).

Definition biv_horner_seqop_rec n n0 k :=
  horner_seqop_rec (map (fun a => a ^~ k) cf) (u ^~ k) n n0.

Definition biv_horner_seqop n k := biv_horner_seqop_rec n n k.

Lemma biv_horner_seqopP
  (n k : int)
  (biv_cf0 : int -> int -> R := fun _ _ => 0) :
biv_horner_seqop n k =
  \sum_(0 <= j < size cf) nth biv_cf0 cf j n k * u (int.shift j n) k.
Proof.
rewrite -[LHS]/(horner_seqop [seq a ^~ k | a <- cf] (u ^~ k) n).
rewrite horner_seqopP size_map [LHS]big_seq_cond [RHS]big_seq_cond.
apply: eq_bigr=> i /andP []; rewrite mem_index_iota=> /andP [_ hi] _.
by rewrite (nth_map biv_cf0).
Qed.

End BivHorner.

Section BivHorner2.

Variables (cf : seq (seq (int -> int -> R))) (u : int -> int -> R).

Definition biv_horner_seqop2 : (int -> int -> R) -> int -> int -> R :=
  foldr
    (fun a r u n k =>
      let u' := fun n_ k_ : int => u n_ (int.shift 1%N k_) in
      r u' n k + biv_horner_seqop a u n k)
    (fun u n k => 0) cf.

Lemma biv_horner_seqop2P
  (n k : int)
  (biv_cf0 : int -> int -> R := fun _ _ => 0) :
biv_horner_seqop2 u n k =
  \sum_(0 <= i < size cf)
    \sum_(0 <= j < size (nth [::] cf i))
       nth biv_cf0 (nth [::] cf i) j n k * u (int.shift j n) (int.shift i k).
Proof.
rewrite /biv_horner_seqop2; elim: cf u => [ | cf0 c ihc] u'.
  by rewrite /= big_nil.
by rewrite /= {}ihc biv_horner_seqopP /= big_nat_recl //= addrC.
Qed.

Lemma biv2univ_horner_seqopP
  (n k : int)
  (biv_cf0 : int -> int -> R := fun _ _ => 0) :
biv_horner_seqop2 u n k =
  \sum_(0 <= i < size cf)
    horner_seqop (map (fun a => a ^~ k) (nth [::] cf i))
      (fun a => u a (int.shift i k)) n.
Proof.
rewrite biv_horner_seqop2P [LHS]big_seq_cond [RHS]big_seq_cond.
apply: eq_bigr=> i /andP []; rewrite mem_index_iota=> /andP [_ hi] _.
rewrite horner_seqopP size_map [LHS]big_seq_cond [RHS]big_seq_cond.
apply: eq_bigr=> j /andP []; rewrite mem_index_iota=> /andP [_ hj] _.
by rewrite (nth_map biv_cf0).
Qed.

End BivHorner2.


Variable u : int -> int -> int -> R.
Variable Pseq : seq (seq (int -> int -> R)).
Variable Q : (int -> int -> int -> R) -> (int -> int -> int -> R).
Variables (a b : int).
Variable not_D : int -> int -> int -> bool.

(* The intended use of biv_sound_telescoping is by providing PeqDQ, all other
   arguments being implicit.  Here, n is a parameter and k plays the
   role of n in sound_telescoping above. *)
Lemma biv_sound_telescoping
  (biv_cf0 : int -> int -> R := fun _ _ => 0)
  (s : nat := size Pseq)
  (r : nat := foldr maxn 0%N (map size Pseq))
  (P : (int -> int -> R) -> int -> int -> R := biv_horner_seqop2 Pseq)
  (U : int -> int -> R := fun n k => \sum_(a <= m < k + b :> int) u n k m)
  (n k : int)
  (range_correct : a <= k + b)
  (PeqDQ :
    forall (n k m : int), not_D n k m ->
      P (pfun2 u m) n k = Q u n k (int.shift 1 m) - Q u n k m) :
P U n k =
Q u n k (k + b) - Q u n k a +
\sum_(a <= m < k + b :> int | ~~ not_D n k m)
  (P (pfun2 u m) n k - (Q u n k (int.shift 1 m) - Q u n k m)) +
\sum_(0 <= i < s)
  \sum_(0 <= j < size (nth [::] Pseq i))
    \sum_(0 <= l < i)
      nth biv_cf0 (nth [::] Pseq i) j n k *
        u (int.shift j n) (int.shift i k) (int.shift l (k + b)).
Proof.
set PUnk := P U n k.
set DeltaQ := (X in PUnk = X + _ + _).
set exceptions := (X in PUnk = DeltaQ + X + _).
set excess := (X in PUnk = DeltaQ + exceptions + X).
set rhs := (X in _ = X).

have PUnk_value :
    PUnk =
    \sum_(0 <= i < s)
      \sum_(0 <= j < size (nth [::] Pseq i))
        nth biv_cf0 (nth [::] Pseq i) j n k *
        (\sum_(a <= m < k + b :> int)
           u (int.shift j n) (int.shift i k) m +
         \sum_(k + b <= m < k + b + Posz i :> int)
           u (int.shift j n) (int.shift i k) m).
  rewrite /PUnk /P /U biv_horner_seqop2P.

  rewrite big_nat_cond [in RHS]big_nat_cond.
  apply: eq_bigr => i.  rewrite andbT -/s.  move/andP=> [_ i_bound].
  apply: eq_bigr => j _.
  congr (_ * _).
  rewrite -big_cat_int ?cpr_add //=.
  by rewrite !int.shift2Z addrAC.

have {PUnk_value} PUnk_value :
    PUnk =
    \sum_(a <= m < k + b :> int)
      \sum_(0 <= i < s)
        \sum_(0 <= j < size (nth [::] Pseq i))
          nth biv_cf0 (nth [::] Pseq i) j n k *
            u (int.shift j n) (int.shift i k) m +
    \sum_(0 <= i < s)
      \sum_(0 <= j < size (nth [::] Pseq i))
        \sum_(0 <= m < i)
          nth biv_cf0 (nth [::] Pseq i) j n k *
            u (int.shift j n) (int.shift i k) (int.shift m (k + b)).
  rewrite {}PUnk_value.
  do 2! (rewrite [in RHS]exchange_big /= -big_split /=; apply: eq_bigr => ? _).
  rewrite -2!mulr_sumr -mulrDr.  congr (_ * (_ + _)).
  rewrite -{1}[k + b]add0r big_addz /=.
  rewrite !int.shift2Z addrAC subrr add0r eq_big_int_nat /=.
  by apply: eq_bigr=> i; rewrite int.shift2Z [Posz i + _]addrC.

set sum1 := (X in PUnk = X + _) in PUnk_value.
have sum1_value : sum1 = \sum_(a <= m < k + b :> int) P (pfun2 u m) n k.
  apply: eq_bigr => m _.
  by rewrite /P /U biv_horner_seqop2P -/s /pfun2.
rewrite {}sum1_value {sum1} in PUnk_value.

have split_sum_of_P :
    \sum_(a <= m < k + b :> int) P (pfun2 u m) n k =
    \sum_(a <= m < k + b :> int | not_D n k m)
      (Q u n k (int.shift 1 m) - Q u n k m) +
    \sum_(a <= m < k + b :> int | ~~ not_D n k m) P (pfun2 u m) n k.
  rewrite (bigID (not_D n k)) /=.
  congr (_ + _).
  apply: eq_bigr => m not_D_m.
  by apply: PeqDQ.
rewrite {}split_sum_of_P in PUnk_value.

rewrite {}PUnk_value.
congr (_ + _).
rewrite -[X in _ + X]add0r addrA.
pose complement :=
  \sum_(a <= m < k + b :> int | ~~ not_D n k m)
    (Q u n k (int.shift 1 m) - Q u n k m).
rewrite -[X in _ + X + _](subrr complement).
rewrite addrA -addrA.
congr (_ + _).
  rewrite -(bigID (not_D n k) predT) /=.
  by rewrite telescopez.
rewrite -[complement]mul1r -mulNr.
rewrite /complement big_distrr /=.
rewrite -big_split /=.
rewrite /exceptions.
apply: eq_bigr => m _.
by rewrite mulNr mul1r addrC.
Qed.

End CreativeTelescopingBivariateMasterLemma.

Arguments sound_telescoping {R u Pseq Q a b not_D n range_correct} PeqDQ.
Arguments biv_sound_telescoping {R u Pseq Q a b not_D n k range_correct} PeqDQ.


(* Extra material for bigopz, not used here, but should maybe be part of the library *)
(* Section ExtraBingInt. *)

(* Variables (RR I : Type) (idx : RR) (op : Monoid.com_law idx). *)

(* Lemma exchange_big_dep_int m1 n1 m2 n2 (PP : pred int) (QQ : rel int) *)
(*                            (xQ : pred int) F : *)
(*     (forall i j, m1 <= i < n1 -> m2 <= j < n2 -> PP i -> QQ i j -> xQ j) -> *)
(*   \big[op/idx]_(m1 <= i < n1 :> int | PP i) \big[op/idx]_(m2 <= j < n2 :> int | QQ i j) F i j = *)
(*     \big[op/idx]_(m2 <= j < n2 :> int | xQ j) *)
(*        \big[op/idx]_(m1 <= i < n1 :> int | PP i && QQ i j) F i j. *)
(* Proof. *)
(* move=> PQxQ. *)
(* rewrite (@eq_bigr _ _ _ _ _ _ _ _ (fun _ _ => @big_seq_cond _ _ _ _ _ _ _)). *)
(* rewrite big_seq_cond /= (exchange_big_dep xQ) => [ | i j]; last first. *)
(*   by rewrite !mem_index_iotaz => /andP[mn_i Pi] /andP[mn_j /PQxQ->]. *)
(* rewrite 2!(@big_seq_cond _ _ _ _ _ xQ); apply: eq_bigr => j /andP[-> _] /=. *)
(* by rewrite [rhs in _ = rhs]big_seq_cond; apply: eq_bigl => i; rewrite -andbA. *)
(* Qed. *)

(* Implicit Arguments exchange_big_dep_int [m1 n1 m2 n2 PP QQ F]. *)

(* Lemma exchange_big_int m1 n1 m2 n2 (PP QQ : pred int) F : *)
(*   \big[op/idx]_(m1 <= i < n1 :> int | PP i) \big[op/idx]_(m2 <= j < n2 :> int | QQ j) F i j = *)
(*     \big[op/idx]_(m2 <= j < n2 :> int | QQ j) \big[op/idx]_(m1 <= i < n1 :> int | PP i) F i j. *)
(* Proof. *)
(* rewrite (exchange_big_dep_int QQ) //. *)
(* by apply: eq_bigr => i /= Qi; apply: eq_bigl => j; rewrite Qi andbT. *)
(* Qed. *)

(* End ExtraBingInt. *)
