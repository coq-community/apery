From mathcomp Require Import all_ssreflect all_algebra.

Require Import extra_mathcomp.

Import Order.TTheory GRing.Theory Num.Theory.

Open Scope nat_scope.

Local Notation "s `_ i" := (nth 0 s i) : nat_scope.

(* For n_1, ..., n_k, and n := n_1 + ... + n_k, the multinomial (n | n_1, ... n_k) is
the coefficient of the monomial x_1 ^ n_1 ... x_k ^n_k in the expansion of
(x_1 + ... + x_k)^n. It can also be defined as n! /(n_1!... n_k!) or as the product
(bin n_1 n_2) (bin (n_1 + n_2) n_2)... (bin n n_k) *)

(* Shall we obtain this from a more computational friendly
  definition? One day, may be, if needed. *)
Definition multinomial (l : seq nat) : nat :=
 \prod_(0 <= i < size l) (binomial (\sum_(0 <= j < i.+1) l`_j) l`_i).

Arguments multinomial l : simpl never.

(* Notation under evaluation ... *)
Notation "''C' [ l ]" := (multinomial l)
  (at level 8, format "''C' [ l ]") : nat_scope.

(* For instance I would like to avoid double brackets, like in: *)
Check 'C[[::]].
Check 'C[[:: 8]].

(* Unlocking is needed for computation and for convertibility. *)
Example foo : multinomial [::1;2] = 3.
by rewrite /multinomial /binomial unlock.
Qed.

Lemma multi_nil : 'C[[::]] = 1.
Proof. by rewrite /multinomial big_nil. Qed.

Lemma multi_singl n : 'C[[:: n]] = 1.
Proof.
by rewrite /multinomial; do 2! (rewrite !big_mkord /= big_ord1 /=); rewrite binn.
Qed.

Lemma multi_gt0 l : 'C[l] > 0.
Proof. by apply: prodn_gt0 => i; rewrite bin_gt0 big_nat_recr //= leq_addl. Qed.

Lemma multi_rcons n l :
'C[rcons l n] = 'C[l] * 'C(\sum_(j <- l) j + n, n).
Proof.
rewrite [in LHS]/multinomial [in RHS](big_nth 0) size_rcons !big_nat_recr //=.
have -> : (rcons l n)`_(size l) = n by rewrite nth_rcons ltnn eqxx.
have aux k : 0 <= k < size l -> (rcons l n)`_k = l`_k.
  by rewrite nth_rcons; case/andP=> _ ->.
rewrite !big_nat (eq_bigr _ aux) -big_nat; congr (_ * _); rewrite /multinomial.
rewrite !big_nat; apply: eq_bigr => i ?; rewrite aux // !big_nat; congr 'C(_, _).
by apply: eq_bigr=> j /andP[le0j leji]; rewrite aux // le0j (leq_trans leji).
Qed.

Lemma multi_prod_fact l : 'C[l] * \prod_(j <- l) j`! = (\sum_(j <- l) j)`!.
Proof.
elim/last_ind: l => [| l n ihl]; first by rewrite multi_nil !big_nil.
set p := \prod_(_ <- _) _; set s := \sum_(_ <- _) _.
rewrite multi_rcons mulnAC.
have aux : (rcons l n)`_(size l) = n by rewrite nth_rcons ltnn eqxx.
have -> : p = \prod_(j <- l) j`! * n`! by rewrite /p -cats1 big_cat /= big_seq1.
rewrite mulnA ihl.
have es : s = \sum_(j <- l) j + n by rewrite /s -cats1 big_cat /= big_seq1.
rewrite -es mulnC [X in _ * X = _]mulnC.
have -> : \sum_(j <- l) j = s - n by rewrite es addnK.
by rewrite bin_fact // es leq_addl.
Qed.

Notation "'BIG_op_F' op" :=
  (F in  \big[op/_]_(i <- _ | _) F i)%pattern (at level 36).

Notation "'BIG_op_P' op" :=
  (P in  \big[op/_]_(i <- _ | P i) _)%pattern (at level 36).


(* For the sake of compatibility with hanson.
Note that the sum and prod should be moved to a \sum_(j <- l)_ shape. *)
Lemma eq_def_multiQ l :
  'C[l]%:Q =
  (\sum_(0 <= i < size l) l`_i)`!%N%:Q /
  (\prod_(0 <= i < size l) (l`_i)`!)%N%:Q.
Proof.
have dn0 : (\prod_(i <- l) i `!)%N%:Q != 0%:Q.
  rewrite pnatr_eq0 -lt0n prodn_gt0 // => i; exact: fact_gt0.
rewrite -(big_nth 0 xpredT) -(big_nth 0 xpredT id). (* booh *)
by rewrite -multi_prod_fact !PoszM !rmorphM /= mulfK.
Qed.

(* Because it is basically mulnK *)
Lemma whyIsThisNotProved (m d n : nat) : ((0 < d) ->  m * d = n -> m = n %/ d)%N.
Proof. by move=> d_gt0 <-; rewrite mulnK. Qed.

(* Compatiblity again. *)
Lemma eq_def_multi1 (l : list nat) :
'C[l] * \prod_(0 <= i < size l) (l`_i)`! = (\sum_(0 <= i < size l) l`_i)`!.
Proof.
rewrite -(big_nth 0 xpredT) -(big_nth 0 xpredT id). (* booh *)
exact: multi_prod_fact.
Qed.


Open Scope ring_scope.

Section Monomials.

Context  {R : unitRingType}.


Definition monomial (x : seq R) (e : seq nat) :=
  \prod_(xi <- zip x e) xi.1 ^ xi.2.


(* Definition monomial {n : nat} (x : seq R) (e : seq 'I_n) := *)
(*   \prod_(xi <- zip x e) xi.1 ^ xi.2. *)


(* Definition monomial {R : unitRingType} {n : nat} (x : seq R) (e : seq 'I_n) := *)
(*   \prod_(0 <= i < size x) (nth 0 x i) ^ (nth 0%N (map (@nat_of_ord n) e) i). *)


Lemma monom_nill e : monomial [::] e = 1.
Proof. by rewrite /monomial zip_nil_l big_nil. Qed.

Lemma monom_nilr (x : seq R) : monomial x [::] = 1.
Proof. by rewrite /monomial zip_nil_r big_nil. Qed.

Lemma monom_rcons (a : R) (x : seq R) i e :
  size x = size e -> monomial (rcons x a) (rcons e i) = (monomial x e) * a ^ i.
Proof. by move => Hxe; rewrite /monomial !zip_rcons // big_rcons. Qed.

End Monomials.


Definition tmap_val {n m} (t : n.-tuple 'I_m) : seq nat :=
  [seq val j | j <- t].

Lemma tmap_val_rcons  {n m} (t : n.-tuple 'I_m) i :
  tmap_val [tuple of rcons t i] = rcons (tmap_val t) i.
Proof. by rewrite /tmap_val map_rcons. Qed.

Section GNewton.

Context  {R : comUnitRingType}.


Lemma generalizedNewton (l : seq R) (n m : nat) (s := size l) :
  (n <= m)%N ->
  (\sum_(x <- l) x) ^+ n =
  \sum_(t : s.-tuple 'I_m.+1 | (\sum_(i <- t) i)%N == n)
   ('C[tmap_val t])%:R * monomial l (tmap_val t).
Proof.
rewrite {}/s; elim/last_ind: l n m => [|l a ihl] n m /=.
- rewrite big_tuple0 big_nil big_tuple big_ord0 /= monom_nill mulr1 /= expr0n.
  by rewrite multi_nil; case: n.
- move=> leqnm; rewrite size_rcons big_rcons /= exprDn.
  set s := size l.
  pose tlast s (t : s.-tuple 'I_m.+1) := last ord0 t.
  have -> P F :
   \sum_(t : s.+1.-tuple 'I_m.+1 | P t) F t =
   \sum_(j < m.+1) \sum_(t | P t && (tlast _ t == j)) F t.
     exact: partition_big.
  pose F (i : nat) := (\sum_(j <- l) j) ^+ (n - i) * a ^+ i *+ 'C(n, i).
  have -> : \sum_(i < n.+1) F i = \sum_(i < m.+1 | (i < n.+1)%N) F i.
    by apply: big_ord_widen; rewrite ltnS.
  rewrite big_mkcond /=; apply: eq_bigr => i _; case: ltnP=> hni; last first.
    rewrite /tlast big_pred0 // => [[]]; case/lastP => // t u stu /=.
    rewrite last_rcons big_rcons /=.
    by apply: contraTF hni; case/andP=> /eqP<- /eqP<-; rewrite -leqNgt leq_addl.
  rewrite {}/F.
  have /ihl -> : (n - i <= m)%N.
    by apply: (leq_trans (leq_subr _ _)); apply: (leq_trans leqnm).
  rewrite mulr_suml -sumrMnl.
  pose tsum a (t : a.-tuple 'I_m.+1) b := ((\sum_(j <- t) j) == b)%N.
  have -> F :
  \sum_(t : s.+1.-tuple 'I_m.+1 | tsum _ t n && (tlast _ t == i)) F t =
  \sum_(t : s.-tuple 'I_m.+1    | tsum _ t (n - i)%N) F [tuple of (rcons t i)].
    pose indx (t : s.-tuple 'I_m.+1) := [tuple of rcons t i].
    pose indxV (t : s.+1.-tuple 'I_m.+1) := [tuple of rev (behead (rev t))].
    rewrite [LHS](reindex indx) /= /tlast /tsum.
       apply: eq_bigl => t; rewrite last_rcons eqxx andbT big_rcons /=.
       apply/eqP/eqP=> [|->]; first exact: (canRL (addnK i)).
       by rewrite subnK.
    exists indxV => t ht; rewrite /indx /indxV /=; apply: val_inj => /=.
      by rewrite rev_rcons revK.
    move: ht; rewrite inE; case/andP=> _; case: t; case/lastP => //= ? j _.
    by rewrite last_rcons => /eqP->; rewrite rev_rcons /= revK.
  symmetry; apply: congr_big => //= u /eqP es /=.
  rewrite tmap_val_rcons multi_rcons natrM mulrAC monom_rcons; last first.
    by rewrite size_map size_tuple.
  by rewrite /tmap_val big_map es exprnP mulr_natr -mulrA subnK.
Qed.


End GNewton.

Section SSRalgMissingInOldButPresentInNew.

Local Open Scope ring_scope.

Variable R : ringType.
Implicit Types x y : R.


End SSRalgMissingInOldButPresentInNew.

Section MultinomialIneq.

Context  {R : comUnitRingType}.

Open Scope nat_scope.


Lemma multinomial_ineq (l : seq nat) (p :=  \prod_(j <- l) j ^ j) (s := \sum_(j <- l) j) :
  'C[l] * p <= s ^ s.
Proof.
  rewrite -lez_nat -!natz natrX natrM natr_sum.
  pose lz : seq int := [seq i%:R | i <- l].
  have -> : (\sum_(i <- l) i%:R = \sum_(i <- lz) i)%R by rewrite big_map.
  pose m := s; pose n := s.
  have /generalizedNewton -> : n <= m by [].
  have paux (i : 'I_(size l)) : nth 0 l i < m.+1.
    rewrite ltnS /m /s.
    have /(big_rem _) -> /= : (nth 0 l i) \in l by rewrite mem_nth.
    exact: leq_addr.
  pose aux (i : 'I_(size l)) := Ordinal (paux i).
  pose tl := mktuple aux.
  have Heq : tmap_val tl = l.
    suff Heq1 (i : 'I_(size l)) : nth 0 (tmap_val tl) i = nth 0 l i.
      apply: (@eq_from_nth nat 0 _ _ ); rewrite size_map size_tuple // .
      move => i Hisize.
      suff -> : nth 0 (tmap_val tl) (Ordinal Hisize) = nth 0 l (Ordinal Hisize) by [].
      exact: Heq1.
    by rewrite (nth_map ord0 0) /tl ?size_tuple ?(nth_mktuple aux ord0 i).
  rewrite /lz size_map; set P := BIG_P.
  have /(bigD1 _) -> /= : P tl.
    rewrite /P /n /s big_tuple big_tnth /=; apply/eqP/eq_bigr => i _.
    by rewrite tnth_mktuple /aux /= (tnth_nth 0) in_tupleE.
  suff {P} -> : (('C[l])%:R * p%:R =
     ('C[tmap_val tl])%:R * monomial [seq i%:R | i <- l] (tmap_val tl) :> int)%R.
  rewrite cpr_add; apply: sumr_ge0 => i _; apply: mulr_ge0.
  - by rewrite ler0n.
  - rewrite /monomial big_seq_cond.
    apply: prodr_ge0 => j; rewrite andbT => /nth_index hj.
    rewrite -(hj (1 : int, 0%N)) nth_zip /=; last first.
      by rewrite !size_map size_tuple.
    rewrite exprn_ge0 //.
    set ll := (X in (0 <= nth _ X _)%R); set k := index _ _.
    case: (ltnP k (size ll)) => [/mem_nth |] hk.
      suff ll_pos x : x \in ll -> (0 <= x)%R by apply: ll_pos.
      rewrite /ll; case/mapP => u _ ->; exact: ler0n.
    by rewrite nth_default.
  congr (_ * _)%R.
  - apply/eqP; rewrite eqr_nat.
    by rewrite Heq.
  - rewrite /monomial /p Heq natr_prod.
    suff -> : zip [seq i%:R | i <- l] l = map (fun i => (Posz i,i)) l.
      rewrite big_map.
      by apply: eq_bigr => i _ /=; first by rewrite natrX -exprnP -natz.
    apply: (@eq_from_nth _ (0%:R,0));rewrite size_zip !size_map minnn// => i Hi.
    rewrite nth_zip ?size_map // ; rewrite (nth_map 0 (Posz 0)) // .
    by rewrite (nth_map 0 (Posz 0,0)) // natz.
Qed.

End MultinomialIneq.
