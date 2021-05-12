From mathcomp Require Import all_ssreflect all_algebra.

Require Import extra_mathcomp.
(* Infrastructure for iterated operators indexed by ints. *)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "\big [ op / idx ]_ ( m <= i < n :> 'int' | P ) F"
  (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <   n  :>  'int'  |   P )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n :> 'int' ) F"
  (at level 36, F at level 36, op, idx at level 10, i, m, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <   n  :>  'int'  ) '/  '  F ']'").

Reserved Notation "\sum_ ( m <= i < n :> 'int' | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  :>  'int'  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n :> 'int' ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  :>  'int' ) '/  '  F ']'").

Reserved Notation "\prod_ ( m <= i < n :> 'int' | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n  :>  'int'  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( m <= i < n :> 'int' ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n  :>  'int' ) '/  '  F ']'").

Import Order.TTheory GRing.Theory Num.Theory.


Open Scope ring_scope.


(* Not sure this is the best definition...*)
Definition index_iotaz_ (mi ni : int) :=
  match mi, ni with
  | Posz _, Negz _ => [::]
  | Posz m, Posz n => map Posz (index_iota m n)
  | Negz m, Negz n => map Negz (rev (index_iota n.+1 m.+1))
  | Negz m, Posz n => rev (map Negz (index_iota 0 m.+1)) ++ (map Posz (index_iota 0 n))
  end.

Definition index_iotaz := nosimpl index_iotaz_.

Lemma index_iotazE : index_iotaz = index_iotaz_. Proof. by []. Qed.


Lemma size_index_iotaz m n : 
  size (index_iotaz m n) = if m <= n then `|n - m|%N else 0%N.
Proof.
case: m => m; case: n => n; rewrite /index_iotaz => //=.
- rewrite size_map /index_iota size_iota.
  case: (leqP n m) => hnm.
  + rewrite lez_nat leq_eqVlt ltnNge hnm orbF; case: ifP.
      by move/eqP->; rewrite subnn subrr.
    by move=> mn; apply/eqP; rewrite subn_eq0.
  + by rewrite lez_nat ltnW // subzn ?(ltnW hnm) // absz_nat.
- by rewrite size_cat size_rev /index_iota /= !size_map !size_iota addnC subn0.
- rewrite size_map size_rev /index_iota size_iota !NegzE ler_opp2 lez_nat.
  rewrite opprK addrC; case: ifP => hnm; first by rewrite subzn.
  case: (altP (n =P m)) => [-> | enm]; first by rewrite subnn.
  apply/eqP; rewrite subn_eq0 ltnNge; move: hnm; rewrite ltnS leq_eqVlt.
  by rewrite (negPf enm) /= => ->.
Qed.


Lemma Negz_inj : injective Negz.
Proof. by move=> ? ? []. Qed.

Lemma mem_index_iotaz m n i : i \in index_iotaz m n = (m <= i < n).
Proof.
case: m => m; case: n => n; rewrite /index_iotaz.
- apply/mapP/idP.
    by case=> xi; rewrite mem_index_iota => hi ->; rewrite ltz_nat.
  by case: i => // xi; rewrite ltz_nat => hi; exists xi; rewrite ?mem_index_iota.
- by rewrite in_nil; case: i => xi //; rewrite andbF.
- rewrite mem_cat; apply/orP/idP => [[] | ].
    + rewrite mem_rev; case/mapP=> xi; rewrite mem_iota add0n; case/andP=> _ hi ->.
      by rewrite andbT !NegzE ler_opp2 /= lez_nat.
    + case/mapP=> xi; rewrite mem_index_iota; case/andP=> _ hi -> /=.
      by rewrite ltz_nat.
  case: i => xi.
  + by rewrite /= => hi; right; apply/mapP; exists xi; rewrite // mem_index_iota.
  + rewrite andbT {1}(NegzE xi) (NegzE m) ler_opp2 => hi; left; rewrite mem_rev.
    rewrite  mem_map ?mem_index_iota //; exact: Negz_inj.
- apply/idP/idP.
    case/mapP=> xi; rewrite mem_rev mem_index_iota => hi ->.
    by rewrite !NegzE  ler_opp2 ltr_opp2 andbC ltz_nat lez_nat.
  case: i => // xi; rewrite !NegzE ler_opp2 ltr_opp2 lez_nat ltz_nat andbC => hi.
  rewrite -NegzE mem_map; last exact: Negz_inj.
  by rewrite mem_rev mem_index_iota.
Qed.

Lemma nth_index_iotaz m n i : m <= n -> (Posz i < `|n - m|) ->
  (index_iotaz m n)`_i = m + (Posz i).
Proof.
case: m => m; case: n => n // hmn hi; rewrite /index_iotaz /=.
- rewrite (nth_map 0%N) /index_iota; last first.
    by rewrite size_iota //; move: hi; rewrite subzn.
  rewrite -natz nth_iota; first by  rewrite natrD !natz.
  suff <- :  `|n - m|%N = (n - m)%N by [].
  by rewrite subzn //; apply/normr_idP; rewrite natz PoszD.
- rewrite nth_cat size_rev /= size_map size_iota.
  case: ifP => him.
  - rewrite nth_rev /= size_map ?size_iota // subSS !NegzE.
    have -> : - Posz (m.+1) + Posz i = - Posz (m - i) -1.
      by rewrite -addn1 PoszD -subzn // opprD opprB addrAC [-Posz m + i]addrC.
    case ek : (m - i)%N => [ | k] //=.
    rewrite (nth_map 0%N).
      rewrite nth_iota; last by rewrite -ek leq_subr.
      by rewrite NegzE -addnS PoszD opprD addrC.
    by rewrite size_iota -ek leq_subr.
  - have {hi} hi : (i - m.+1 < n)%N.
      move: hi; rewrite NegzE opprK -PoszD ger0_norm //.
      by rewrite PoszD -lter_sub_addr subzn ?ltz_nat // ltnNge -ltnS him.
    rewrite (nth_map 0%N); last by rewrite /index_iota size_iota subn0.
    rewrite /index_iota subn0 nth_iota // add0n NegzE addrC subzn //.
    by rewrite ltnNge -ltnS him.
- have {hmn} hmn : (n <= m)%N.
    by  move: hmn; rewrite !NegzE ler_oppl opprK lez_nat.
  have hi' : (i < m - n)%N.
    by move: hi; rewrite !NegzE opprK addrC subzn.
  have hi'' : (i <= m)%N.
    apply: leq_trans (leq_subr n m); exact: ltnW.
  rewrite (nth_map 0%N); last first.
    by rewrite size_rev /index_iota size_iota subSS.
  rewrite /index_iota nth_rev !size_iota ?subSS //.
  rewrite nth_iota; last by rewrite subnSK // leq_subLR leq_addl.
  rewrite !NegzE addnBA // addSn subSS subnKC // -subSn //.
  by rewrite -subzn 1?ltnW // opprB addrC //.
Qed.

Notation "\big [ op / idx ]_ ( m <= i < n :> 'int' | P ) F" :=
  (bigop idx (index_iotaz m n) (fun i : int => BigBody i op P%B F))
     : big_scope.

Notation "\big [ op / idx ]_ ( m <= i < n :> 'int' ) F" :=
  (bigop idx (index_iotaz m n) (fun i : int => BigBody i op true F))
     : big_scope.

Notation "\sum_ ( m <= i < n :> 'int' | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n :> int | P%B) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n :> 'int' ) F" :=
  (\big[+%R/0%R]_(m <= i < n :> int) F%R) : ring_scope.

Notation "\prod_ ( m <= i < n :> 'int' | P ) F" :=
  (\big[*%R/1%R]_(m <= i < n :> int | P%B) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n :> 'int' ) F" :=
  (\big[*%R/1%R]_(m <= i < n :> int) F%R) : ring_scope.


(* This should be obsolete now *)
(* hacking unparsable notations for constant expressions *)
(* Notation "\su 'm_' ( m <= i < n :> 'int' | P ) e" := *)
(*   (\sum_(_ <- (index_iotaz m n) | (fun i => P)) (fun _  => e%R)) *)
(*   (at level 41, e at level 41, *)
(*     format "\su 'm_' ( m  <=  i   < n   :>  'int' |  P ) e") : ring_scope. *)

(* Notation "\pro 'd_' ( m <= i < n :> 'int' | P ) e" := *)
(*   (\prod_(_ <- index_iotaz m n | (fun i => P)) (fun _  => e%R)) *)
(*   (at level 36, e at level 36, *)
(*     format "\pro 'd_' ( m  <=  i   < n   :>  'int' |  P ) e") : ring_scope. *)

Section BigInt.

Variables (R I : Type) (idx : R) (op : Monoid.com_law idx) (r : seq I).


Lemma big_int_cond m n (P : pred int) F :
  \big[op/idx]_(m <= i < n :> int | P i) F i
    = \big[op/idx]_(m <= i < n :> int | (m <= i < n) && P i) F i.
Proof.
by rewrite big_seq_cond; apply: eq_bigl => i; rewrite mem_index_iotaz.
Qed.

Lemma big_int m n F :
  \big[op/idx]_(m <= i < n :> int) F i = \big[op/idx]_(m <= i < n :> int | m <= i < n) F i.
Proof. by rewrite big_int_cond big_andbC. Qed.

Lemma congr_big_int m1 n1 m2 n2 P1 P2 F1 F2 :
    m1 = m2 -> n1 = n2 ->
    (forall i, m1 <= i < n2 -> P1 i = P2 i) ->
    (forall i, P1 i && (m1 <= i < n2) -> F1 i = F2 i) ->
  \big[op/idx]_(m1 <= i < n1 :> int | P1 i) F1 i
    = \big[op/idx]_(m2 <= i < n2 :> int | P2 i) F2 i.
Proof.
move=> <- <- eqP12 eqF12.
rewrite big_seq_cond.
rewrite (@big_seq_cond _ _ _ _ (index_iotaz m1 n1) P2).
apply: eq_big => i; rewrite ?inE /= !mem_index_iotaz.
  by apply: andb_id2l; exact: eqP12.
by rewrite andbC; exact: eqF12.
Qed.

Lemma eq_big_int m n F1 F2 :
    (forall i, m <= i < n -> F1 i = F2 i) ->
  \big[op/idx]_(m <= i < n :> int) F1 i = \big[op/idx]_(m <= i < n :> int) F2 i.
Proof. by move=> eqF; apply: congr_big_int. Qed.

Lemma big_geqz m n (P : pred int) F :
  m >= n -> \big[op/idx]_(m <= i < n :> int | P i) F i = idx.
Proof.
case: m => m; case: n => // n; rewrite index_iotazE ?big_nil //.
  by rewrite lez_nat /index_iotaz_ /index_iota; move/eqnP->; rewrite big_nil.
rewrite ![in _ <= _]NegzE ler_opp2 lez_nat /index_iotaz_ /index_iota; move/eqnP->.
by rewrite big_nil.
Qed.

Lemma eq_big_int_nat m n F :
  \big[op/idx]_(Posz m <= i < Posz n :> int) F i = \big[op/idx]_(m <= i < n) F (Posz i).
Proof. by rewrite /index_iotaz big_map. Qed.

Lemma big_ltz_cond m n (P : pred int) F :
    m < n -> let x := \big[op/idx]_(m + 1 <= i < n :> int | P i) F i in
  \big[op/idx]_(m <= i < n :> int | P i) F i = if P m then op (F m) x else x.
Proof.
case: m => m; case: n => n // hmn.
- by rewrite /= !big_map big_ltn_cond  ?addn1.
- case: m hmn => [_ | m]; rewrite NegzE.
     by rewrite addNr big_map -NegzE index_iotazE /= big_cons big_map.
  rewrite addrC subzSS add0r -!NegzE index_iotazE /index_iotaz_ -(addn1 m.+1).
  by rewrite /index_iota subn0 iota_add map_cat rev_cat add0n /= big_cons.
- case: m hmn => [ | m] //; rewrite !NegzE ltr_opp2 ltz_nat => hmn.
  rewrite addrC subzSS add0r -!NegzE index_iotazE /= /index_iota subSn //.
  by rewrite -[(_ - _).+1]addn1 iota_add rev_cat map_cat subnKC // big_cons.
Qed.

Lemma big_ltz m n F :
     m < n ->
  \big[op/idx]_(m <= i < n :> int) F i = op (F m) (\big[op/idx]_(m + 1 <= i < n :> int) F i).
Proof. move=> lt_mn; exact: big_ltz_cond. Qed.

Lemma PoszN n : - Posz n = if n is m.+1 then Negz m else Posz 0.
Proof. by case: n => [ | n]; rewrite ?oppr0 // NegzE. Qed.

Lemma big_addz m n a (P : pred int) F :
  \big[op/idx]_(m + a <= i < n :> int | P i) F i =
     \big[op/idx]_(m <= i < n - a :> int | P (i + a)) F (i + a).
Proof.
suff -> : index_iotaz (m + a) n = map (fun i => i + a) (index_iotaz m (n - a)).
  by rewrite big_map.
apply: (@eq_from_nth _ 0).
  by rewrite size_map !size_index_iotaz ler_sub_addl addrC -addrA opprD.
move=> i; rewrite size_index_iotaz; case: ifP => // hman hi.
rewrite nth_index_iotaz // (nth_map 0); last first.
  rewrite size_index_iotaz ler_sub_addr hman.
  by move: hi; rewrite opprD -addrCA addrC.
rewrite nth_index_iotaz 1?addrAC // ?ler_sub_addr //.
by move: hi; rewrite opprD addrA.
Qed.

Lemma big_addz2r n a (P : pred int) F :
  \big[op/idx]_(a <= i < n + a :> int | P i) F i =
     \big[op/idx]_(0 <= i < n :> int | P (i + a)) F (i + a).
Proof.
by rewrite -{1}(add0r a) big_addz -addrA subrr addr0.
Qed.

Lemma big_addz2l n a (P : pred int) F :
  \big[op/idx]_(a <= i < a + n :> int | P i) F i =
     \big[op/idx]_(0 <= i < n :> int | P (i + a)) F (i + a).
Proof.
by rewrite -{1}(add0r a) big_addz -addrAC subrr add0r.
Qed.

Lemma big_int_recl n F : 0 < n + 1 ->
  \big[op/idx]_(0 <= i < n + 1 :> int) F i =
     op (F 0) (\big[op/idx]_(0 <= i < n :> int) F (i + 1)).
Proof.
by move=> pSn; rewrite big_ltz // add0r big_addz2r.
Qed.

Set Printing Coercions.

Lemma index_iotaz_add n m p : m <= n -> n <= p ->
(index_iotaz m n ++ index_iotaz n p) = index_iotaz m p.
Proof.
move=> hmn hnp.
have h : `|n - m| + `|p - n| = `|p - m|%N.
  move/leqifP: (leqif_add_distz p n m).
  rewrite hnp hmn orbT addnC; move/eqP; move/(f_equal Posz).
  by rewrite PoszD; move<-.
apply: (@eq_from_nth _ 0); rewrite size_cat !size_index_iotaz hmn hnp.
- rewrite (le_trans hmn hnp); move: h; rewrite -PoszD /=; move/eqP.
  by rewrite eqz_nat; move/eqP.
- move=> i; move: (h); rewrite -PoszD; move/eqP; rewrite eqz_nat.
  move/eqP-> => hi1. rewrite (nth_cat 0) size_index_iotaz.
  rewrite hmn; case: ifP => hi2.
  + by rewrite !nth_index_iotaz //;apply: le_trans hnp.
  have hmn' : `|n - m |  = n - m by apply: ger0_norm; rewrite subr_gte0.
  rewrite nth_index_iotaz //; last first.
    rewrite -subzn; last by  rewrite leqNgt hi2.
    by rewrite lter_sub_addr addrC h ltz_nat.
  rewrite nth_index_iotaz //; last exact: le_trans hnp.
  rewrite -subzn; last by  rewrite leqNgt hi2.
  move: hmn'; rewrite abszE; move->. rewrite addrCA opprB.
  by rewrite [_ + (_ - _)]addrCA subrr addr0 addrC.
Qed.

Lemma big_cat_int n m p (P : pred int) F : m <= n -> n <= p ->
  \big[op/idx]_(m <= i < p :> int | P i) F i = op
   (\big[op/idx]_(m <= i < n :> int | P i) F i)
   (\big[op/idx]_(n <= i < p :> int | P i) F i).
Proof.
by move=> le_mn le_np; rewrite -big_cat /= index_iotaz_add.
Qed.


Lemma big_int_recr m n F : m <= n ->
  \big[op/idx]_(m <= i < n + 1 :> int) F i =
     op  (\big[op/idx]_(m <= i < n :> int) F (i)) (F n).
Proof.
move=> hmn; rewrite (@big_cat_int n) ?ler_paddr //=.
rewrite big_addz2l (@big_ltz 0 1) // add0r (@big_geqz 1 1) // add0r.
by rewrite Monoid.Theory.mulm1.
Qed.

(* Lemma big_int_widen m n1 n2 (P : pred int) F : m <= n1 -> *)
(*      n1 <= n2 -> *)
(*   \big[op/idx]_(m <= i < n1 :> int | P i) F i *)
(*       = \big[op/idx]_(m <= i < n2 :> int | P i && (i < n1 :> int)) F i. *)
(* Proof. *)
(* move=> hmn1 hn12; symmetry; rewrite -big_filter filter_predI big_filter. *)
(* congr bigop; apply: (@eq_from_nth _ 0). *)
(* - rewrite size_index_iotaz hmn1 -count_filter. *)


Lemma big_pred1_eqz m n F j:
\big[op/idx]_(m <= i < n :> int | i == j) F i = if m <= j < n then F j else idx.
Proof.
case: ifP=> hj; last first.
  apply: big_hasC; apply/hasPn => k.
  by rewrite mem_index_iotaz => hk; move/negbT: hj; apply: contra; move/eqP<-.
case/andP: hj => hmj hjn.
rewrite (@big_cat_int _ _ _ _ _ hmj) /=; last by exact: ltW.
rewrite big_hasC; last first.
  by apply/hasPn => k; rewrite mem_index_iotaz; case/andP=> _; apply: ltr_neq.
rewrite Monoid.Theory.mul1m.
rewrite big_ltz_cond // eqxx big_hasC; last first.
  apply/hasPn => k. rewrite mem_index_iotaz; case/andP=> hkj _.
  suff : j < k by rewrite lt_def eq_sym; case/andP.
  by apply: lt_le_trans hkj; rewrite cpr_add.
by rewrite Monoid.Theory.mulm1.
Qed.

Lemma big_or (P1 P2 : pred I) F :
  \big[op/idx]_(i <- r | P1 i || P2 i) F i =
    op
     (\big[op/idx]_(i <- r | P1 i) F i)
     (\big[op/idx]_(i <- r | P2 i && (~~ P1 i)) F i).
Proof.
rewrite (bigID P1).
congr (op _ _); apply: eq_bigl => i; by case: (P1 i); case: (P2 i).
Qed.

Lemma big_nat_widen_lr (m1 m2 n1 n2 : nat) (P : pred nat) F :
  (m2 <= m1)%N -> (n1 <= n2)%N ->
  \big[op/idx]_(m1 <= i < n1 | P i) F i
    = \big[op/idx]_(m2 <= i < n2 | P i && (m1 <= i < n1)%N) F i.
Proof.
move=> len12 len21; symmetry; rewrite -big_filter filter_predI big_filter.
have [ltn_trans eq_by_mem] := (ltn_trans, irr_sorted_eq ltn_trans ltnn).
congr bigop; apply: eq_by_mem; rewrite ?sorted_filter ?iota_ltn_sorted // => i.
rewrite mem_filter !mem_index_iota; apply/idP/idP; first by case/and3P.
move=> himn; rewrite himn; case/andP: himn => h1 h2.
by rewrite (leq_trans _ h1) // (leq_trans _ len21).
Qed.


Lemma eq_big_int_nat_cond m n F P :
  \big[op/idx]_(Posz m <= i < Posz n :> int | P i) F i =
  \big[op/idx]_(m <= i < n | P (Posz i)) F (Posz i).
Proof. by rewrite /index_iotaz big_map. Qed.

End BigInt.


Section TelescopeSum.

Variable R : ringType.

Lemma telescopez a b (f : int -> R) : a <= b ->
  \sum_(a <= k < b :> int) (f (k + 1) - f k) = f b - f a.
Proof.
rewrite -{2}[a]add0r big_addz => hab /=.
case e: (b - a) => [bma | bma]; last by move: hab; rewrite -subr_ge0 e.
rewrite eq_big_int_nat /=.
transitivity (\sum_(0 <= i < bma) (f (Posz (i + 1)%N + a) - f (Posz i + a))).
  apply: congr_big_nat => // i _ ; by rewrite PoszD addrAC.
by rewrite (telescope_nat (fun i => f (Posz i + a))%R) // add0r -e addrNK.
Qed.

End TelescopeSum.


Section TelescopeProd.

Variable R : fieldType.


Lemma telescope_prod_int (a b : int) (f : int -> R) :
 (forall k, a <= k < b -> f k != 0) ->  a < b ->
  \prod_(a <= k < b :> int) (f (k + 1) / f k) = f b / f a.
Proof.
move=> hf; rewrite -{2}[a]add0r big_addz => hab /=.
case e: (b - a) => [bma | bma]; last by move: hab; rewrite -subr_gt0 e.
rewrite eq_big_int_nat /=.
transitivity (\prod_(0 <= i < bma) (f (Posz (i + 1)%N + a) / f (Posz i + a))).
  apply: congr_big_nat => // i _ ; by rewrite PoszD addrAC.
rewrite (@telescope_prod_nat _ _ _ (fun i => f (Posz i + a))%R) //.
- by rewrite add0r -e addrNK.
- move=> k /andP [h0k hbma]; apply: hf; rewrite ler_addr -ltr_subr_addr e.
  by rewrite lez_nat ltz_nat h0k /=.
- have : 0 < b - a by rewrite subr_gt0.
  by rewrite e ltz_nat.
Qed.

End TelescopeProd.
