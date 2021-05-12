From mathcomp Require Import all_ssreflect all_algebra.
(* Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path div choice. *)
(* Require Import fintype tuple finfun bigop prime finset binomial. *)
(* Require Import ssralg ssrnum ssrint intdiv rat. *)

From mathcomp Require Import bigenough.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory BigEnough.

Open Scope ring_scope.

Section AlgCMissing.

Lemma ler1q (F : numFieldType) x: (1 <= ratr x :> F) = (1 <= x).
Proof. by rewrite (_ : 1 = ratr 1) ?ler_rat ?rmorph1. Qed.

Lemma lerq1 (F : numFieldType) x: (ratr x <= 1 :> F) = (x <= 1).
Proof. by rewrite (_ : 1 = ratr 1) ?ler_rat ?rmorph1. Qed.

Lemma ltrq1 (F : numFieldType) x: (ratr x < 1 :> F) = (x < 1).
Proof. by rewrite (_ : 1 = ratr 1) ?ltr_rat ?rmorph1. Qed.

Lemma ltr1q (F : numFieldType) x: (1 < ratr x :> F) = (1 < x).
Proof. by rewrite (_ : 1 = ratr 1) ?ltr_rat ?rmorph1. Qed.

End AlgCMissing.

(* FIXME : are these lemmas missing in MathComp? *)

(* Suggestions for alternative statements of lemmas in big_op: *)
Section AltBigOp.

Variables  (R : Type) (idx : R) (op : Monoid.law idx).

Lemma big_nat_recr_alt (n m : nat) (F : nat -> R) : (m <= n)%N ->
\big[op/idx]_(m <= i < n.+1) F i = op (\big[op/idx]_(m <= i < n) F i) (F n).
Proof. by move=> lemn; rewrite (@big_cat_nat _ _ _ n) //= big_nat1. Qed.

Lemma big_nat_recl_alt (n m : nat) (F : nat -> R) : (m <= n)%N ->
  \big[op/idx]_(m <= i < n.+1) F i =
     op (F m) (\big[op/idx]_(m <= i < n) F i.+1).
Proof. by move=> lemn; rewrite big_ltn // big_add1. Qed.

End AltBigOp.

Section ExtraInt.

Lemma expfV (R : idomainType) (x : R) (i : int) : (x ^ i) ^-1 = (x ^-1) ^ i.
Proof. by rewrite invr_expz exprz_inv. Qed.

End ExtraInt.


Section ExtraRat.

(* Two technical lemmas about rationals that are integers *)
(* FIXME: They could be turned into equivalences although this is not needed*)
(* here. We do not do this to avoid a side condition on d != 0, and because*)
(* the other direction seems less usefull *)
Lemma Qint_dvdz (m d : int) : (d %| m)%Z -> ((m%:~R / d%:~R : rat) \is a Qint).
Proof.
case/dvdzP=> z ->; rewrite rmorphM /=; case: (altP (d =P 0)) => [->|dn0].
  by rewrite mulr0 mul0r.
by rewrite mulfK ?intr_eq0 // rpred_int.
Qed.

Lemma Qnat_dvd (m d : nat) : (d %| m)%N -> ((m%:R / d%:R : rat) \is a Qnat).
Proof.
move=> h; rewrite Qnat_def divr_ge0 ?ler0n // -[m%:R]/(m%:~R) -[d%:R]/(d%:~R).
by rewrite Qint_dvdz.
Qed.

Lemma denqVz (i : int) : i != 0 -> denq (i%:~R^-1) = `|i|.
Proof.
by move=> h; rewrite -div1r -[1]/(1%:~R) coprimeq_den /= ?coprime1n // (negPf h).
Qed.

End ExtraRat.

Section ExtraSsrNum.

Variable R : numDomainType.

Lemma ler1z (n : int) : (1 <= n%:~R :> R) = (1 <= n).
Proof. by rewrite -[1]/(1%:~R) ler_int. Qed.

Lemma ltr1z (n : int) : (1 < n%:~R :> R) = (1 < n).
Proof. by rewrite -[1]/(1%:~R) ltr_int. Qed.

Lemma ltr_neq (x y : R) : x < y -> x != y.
Proof. by rewrite lt_def eq_sym; case/andP. Qed.

Lemma lt0r_neq0 (x : R) : 0 < x  -> x != 0.
Proof. by move => ?; rewrite eq_sym ltr_neq. Qed.

Lemma ltr0_neq0 (x : R) : x < 0  -> x != 0.
Proof. by move => Hx; rewrite ltr_neq. Qed.

Lemma expN1r (i : int) : (-1 : R) ^ i = (-1) ^+ `|i|.
Proof.
case: i => n; first by rewrite exprnP absz_nat.
by rewrite NegzE abszN  absz_nat -invr_expz expfV invrN1.
Qed.

Lemma ltr_prod (E1 E2 : nat -> R) (n m : nat) :
   (m < n)%N -> (forall i, (m <= i < n)%N -> 0 <= E1 i < E2 i) ->
  \prod_(m <= i < n) E1 i < \prod_(m <= i < n) E2 i.
Proof.
elim: n m => // n ihn m; rewrite ltnS leq_eqVlt; case/orP => [/eqP -> | ltnm hE].
  by move/(_ n) => /andb_idr; rewrite !big_nat1 leqnn ltnSn /=; case/andP.
rewrite big_nat_recr_alt ?[X in _ < X]big_nat_recr_alt ?leqW //=.
move/andb_idr: (hE n); rewrite leqnn ltnW //=; case/andP => h1n h12n.
rewrite big_nat_cond [X in _ < X * _]big_nat_cond; apply: ltr_pmul => //=.
- apply: prodr_ge0 => i; rewrite andbT; case/andP=> hm hn.
  by move/andb_idr: (hE i); rewrite hm /= ltnS ltnW //=; case/andP.
rewrite -!big_nat_cond; apply: ihn => // i /andP [hm hn]; apply: hE.
by rewrite hm ltnW.
Qed.

End ExtraSsrNum.

(*** Two lemmas about geometric sequences. We just use the second one. ***)
Section ExtraGeom.

(* FIXME : these two lemmas are not cleaned up *)
(* The proof uses bigenough so that's not strictly in MathComp, but *)
(* as usual we could eliminate the pose_big_enough a posteriori. *)
Lemma Gseqgt1 (r : rat)(E : rat) : 0 <= E -> 1 < r ->
  exists N : nat, forall n : nat, (N <= n)%nat -> E < r ^ n.
Proof.
move=> ge0E lt1r.
pose_big_enough M.
  exists M => k hMk.
  have le1r : 1 <= r by rewrite ltW.
  have {lt1r} lt1r : 0 < r - 1 by rewrite subr_gt0.
  suff aux (n : nat) : n%:~R * (r - 1) - 1 <= r ^ n.
    apply: lt_le_trans (aux k); rewrite -ltr_sub_addr opprK -ltr_pdivr_mulr //.
    have h : 0 <= (E + 1) / (r - 1).
       apply: divr_ge0; by [exact:  addr_ge0 | exact: ltW].
    by apply: lt_trans (archi_boundP h) _; rewrite ltr_nat.
  elim: n => [|n ihn]; first by rewrite mul0r add0r expr0z.
  have -> : n.+1%:~R * (r - 1) - 1 = n%:~R * (r - 1) - 1 + (r - 1).
    by rewrite -addn1 PoszD rmorphD /= mulrDl mul1r addrAC.
  have -> : r ^ n.+1 = r ^ n + (r ^ n.+1 - r ^ n) by rewrite addrCA addrN addr0.
  apply: ler_add => //.
  have -> : r ^ n.+1 - r ^ n = r ^ n * (r - 1).
    by rewrite mulrDr mulrN mulr1 -exprnP exprSr.
  case: n {ihn} => [| n ]; first by rewrite mul1r.
  rewrite ler_pmull // -exprnP expr_ge1 //; exact: le_trans le1r.
by close.
Qed.

Lemma Gseqlt1 (r : rat)(eps : rat) : 0 < eps -> 0 < r < 1 ->
  exists N : nat, forall n : nat, (N <= n)%nat -> r ^ n < eps.
Proof.
move=> ge0eps /andP [lt0r ltr1].
have hE : 0 <= eps ^-1 by apply/ltW; rewrite invr_gt0.
have hr : 1 < r ^-1 by rewrite invf_gt1.
have [M hM] := Gseqgt1 hE hr; exists M => n hMn.
rewrite -ltf_pinv //; first by rewrite invr_expz -exprz_inv; exact: hM.
exact: exprz_gt0.
Qed.

End ExtraGeom.


Section Telescope.

Variable R : zmodType.

Lemma telescope_nat (a b : nat) (f : nat -> R) : (a <= b)%N ->
  \sum_(a <= k < b) (f (k + 1)%N - f k) = f b - f a.
Proof.
rewrite -{2}[a]add0n big_addn; elim: b => [ | b ihb].
  by rewrite leqn0=> /eqP ->; rewrite subrr subnn big_mkord big_ord0.
rewrite leq_eqVlt; case/orP=> [/eqP -> | a_lt_b1].
  by rewrite subnn subrr big_geq.
rewrite subSn ?big_nat_recr //= ihb ?subnK // addn1 addrC -addrA [- _ + _]addrA.
by rewrite addNr sub0r.
Qed.

End Telescope.


Section TelescopeProd.

Variable R : fieldType.

Lemma telescope_prod_nat (a b : nat) (f : nat -> R) :
 (forall k, (a <= k < b)%N -> f k != 0) ->  (a < b)%N ->
  \prod_(a <= k < b) (f (k + 1)%N / f k) = f b / f a.
Proof.
move=> hf; rewrite -{2}[a]add0n big_addn; elim: b hf => [ | b ihb] hf //.
rewrite ltnS leq_eqVlt; case/orP=> [/eqP -> | a_lt_b1].
  by rewrite subSn // subnn big_nat_recr //= big_nil mul1r add0n addn1.
rewrite subSn ?big_nat_recr //= ihb ?subnK //; last first.
  by move=> k /andP [hak hkb]; apply: hf; rewrite hak ltnS ltnW.
rewrite addn1 -!mulrA mulrC -!mulrA mulVf; first by rewrite mulr1 mulrC.
by apply: hf; rewrite ltnW //=.
Qed.

End TelescopeProd.


Section ExtraZip.

Variables S T : Type.

Lemma zip_nil_l  (t : seq T) : zip ([::] : seq S) t = [::].
Proof. by case: t. Qed.

Lemma zip_nil_r  (s : seq S) : zip s ([::] : seq T) = [::].
Proof. by case: s. Qed.

End ExtraZip.


Section ExtraBigOp.

Lemma big_tuple0 R idx (op : Monoid.law idx) (I : finType) P (F : 0.-tuple I -> R) :
  \big[op/idx]_(t : 0.-tuple I | P t) F t = if P [tuple] then F [tuple] else idx.
Proof.
rewrite big_mkcond (big_pred1 [tuple]) // => x /=; rewrite tuple0 (eqxx [tuple]).
by [].
Qed.

Lemma big_rcons T R idx (op : Monoid.law idx) i r (P : pred T) (F : T -> R) :
    let x := \big[op/idx]_(j <- r | P j) F j in
  \big[op/idx]_(j <- rcons r i | P j) F j = if P i then op x (F i) else x.
Proof.
rewrite -cats1 big_cat /= [in X in op _ X]big_mkcond big_seq1.
by case: ifP=> //; rewrite Monoid.mulm1.
Qed.

End ExtraBigOp.

Section ExtraTruncLog.

Local Open Scope nat_scope.

Lemma trunc_logn0 n : trunc_log n 0 = 0. Proof. by case: n => // [] []. Qed.

(* See also inlined stuff in proof of Lemma 2. *)
End ExtraTruncLog.
