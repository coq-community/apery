From mathcomp Require Import all_ssreflect all_algebra.

From mathcomp Require Import bigenough cauchyreals.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory BigEnough.

Open Scope ring_scope.

Section ExtraCreals.

Variable F : realFieldType.

Local Open Scope ring_scope.

Lemma eq_creal_ext (x y : creal F) : x =1 y ->  (x == y)%CR.
Proof.
move=> heq; apply/eq_crealP; exists (fun _ => 0%N) => * /=.
by rewrite heq subrr normr0.
Qed.

Lemma ler_lecr  (x y : creal F) : (forall i, x i <= y i) ->  (x <= y)%CR.
Proof.
move=> heq; apply: (@le_crealP _ 0%N) => j _; exact: heq.
Qed.


Lemma ltcr_add2r (z x y : creal F) : (x < y)%CR -> (x + z < y + z)%CR.
Proof.
move=> lt_xy; pose_big_enough i.
  apply: (@lt_crealP _ (diff lt_xy) i i); rewrite ?diff_gt0 //=.
  by rewrite addrAC ler_add2r diffP.
by close.
Qed.

Lemma ltcr_add2l (z x y : creal F) : (x < y)%CR -> (z + x < z + y)%CR.
Proof.
move=> lt_xy; pose_big_enough i.
  apply: (@lt_crealP _ (diff lt_xy) i i); rewrite ?diff_gt0 //=.
  rewrite -addrA ler_add2l diffP //.
by close.
Qed.

Lemma addr_gtcr0 (x y : creal F) : (0 < x -> 0 < y -> 0 < x + y)%CR.
move=> lt_0x lt_0y.
have := ltcr_add2r y lt_0x; rewrite add_0creal => h.
by apply: lt_creal_trans h.
Qed.

Lemma subcr_eq0  (x y : creal F) : (x - y == 0)%CR <-> (x == y)%CR.
Proof.
split => h.
  rewrite -[y]add_creal0 -h; apply: eq_creal_ext=> i /=; rewrite addrCA subrr.
  by rewrite addr0.
by rewrite h; apply: eq_creal_ext=> i /=; rewrite subrr.
Qed.

Lemma ltcr_mul2r (z x y : creal F) : 
  (x < y)%CR -> (0 < z)%CR -> (x * z < y * z)%CR.
Proof.
move=> ltxy lt0z; pose_big_enough i.
  apply: (@lt_crealP _ ((diff ltxy) * (diff lt0z)) i i) => //=.
  - apply: mulr_gt0; exact: diff_gt0.
  rewrite -ler_sub_addl -mulrBl; apply: ler_pmul.
  - by apply: ltW; apply: diff_gt0.
  - by apply: ltW; apply: diff_gt0.
  - by rewrite ler_sub_addl diffP.
  - by rewrite -[X in X <= _]add0r -[0]/((0%:CR)%CR i) diffP.
by close.
Qed.

Lemma mulcrN (x y : creal F) : (x * - y == - (x * y))%CR.
Proof. by apply: eq_creal_ext=> i /=; rewrite mulrN. Qed.

Lemma mulNcr (x y : creal F) : (- x * y == - (x * y))%CR.
Proof. by apply: eq_creal_ext=> i /=; rewrite mulNr. Qed.

Lemma mulcrC (x y : creal F) : (x * y == y * x)%CR.
Proof. by apply: eq_creal_ext=> i /=; rewrite mulrC. Qed.

Lemma mulcrA (x y z : creal F) : (x * (y * z) == x * y * z)%CR.
Proof. by apply: eq_creal_ext=> i /=; rewrite mulrA. Qed.

Lemma addcrC (x y : creal F) : (x + y == y + x)%CR.
Proof. by apply: eq_creal_ext=> i /=; rewrite addrC. Qed.

Lemma addcrA (x y z : creal F) : (x + (y + z) == x + y + z)%CR.
Proof. by apply: eq_creal_ext=> i /=; rewrite addrA. Qed.

Lemma addcrN (x : creal F) : (x - x == 0)%CR.
Proof. by apply: eq_creal_ext=> i /=; rewrite addrN. Qed.

Lemma mulcrDr (x y z : creal F) : (x * (y + z) == x * y + x * z)%CR.
Proof. by apply: eq_creal_ext=> i /=; rewrite mulrDr. Qed.

Lemma mulcrDl (x y z : creal F) : ((y + z) * x == y * x + z * x)%CR.
Proof. by apply: eq_creal_ext=> i /=; rewrite mulrDl. Qed.

Lemma ltcr_mul2l (z x y : creal F) : 
  (x < y)%CR -> (0 < z)%CR -> (z * x < z * y)%CR.
Proof. rewrite ![(z * _)%CR]mulcrC; exact: ltcr_mul2r. Qed.


Lemma ltcr_pmul (x1 y1 x2 y2 : creal F) :
      (0 < x1)%CR -> (0 < y2)%CR -> (x1 < y1)%CR -> (x2 < y2)%CR -> 
      (x1 * x2 < y1 * y2)%CR.
Proof.
move=> px1 px2 lt1 lt2.
have aux : (x1 * x2 < x1 * y2)%CR by apply: ltcr_mul2l.
by apply: lt_creal_trans aux _; apply: ltcr_mul2r.
Qed.

Lemma mulr_gtcr0 (x y : creal F) : (0 < x -> 0 < y -> 0 < x * y)%CR.
move=> lt_0x lt_0y; pose_big_enough i.
  apply: (@lt_crealP _ ((diff lt_0x) * (diff lt_0y)) i i) => //=.
  - apply: mulr_gt0; exact: diff_gt0.
  rewrite add0r; apply: ler_pmul.
  - by apply: ltW; apply: diff_gt0.
  - by apply: ltW; apply: diff_gt0.
  - by rewrite -[X in X <= _]add0r -[0]/((0%:CR)%CR i) diffP.
  - by rewrite -[X in X <= _]add0r -[0]/((0%:CR)%CR i) diffP.
by close.
Qed.

Lemma cst_crealM (x y : F) : ((x * y)%:CR == x%:CR * y%:CR)%CR.
Proof. by apply: eq_creal_ext=> i /=. Qed.

Lemma cst_crealD (x y : F) : ((x + y)%:CR == x%:CR + y%:CR)%CR.
Proof. by apply: eq_creal_ext=> i /=. Qed.

Lemma cst_crealB (x y : F) : ((x - y)%:CR == x%:CR - y%:CR)%CR.
Proof. by apply: eq_creal_ext=> i /=. Qed.

Lemma cst_crealN (x : F) : ((- x)%:CR == - x%:CR)%CR.
Proof. by apply: eq_creal_ext=> i /=. Qed.

Lemma le_ubound (x : creal F) : (x <= (ubound x)%:CR)%CR.
Proof.
apply: (@le_crealP _ 0%N) => j _ /=.
apply: le_trans (uboundP x j); exact: ler_norm.
Qed.

Lemma lt_ubound (x : creal F) : (x < (ubound x + 1)%:CR)%CR.
Proof.
pose_big_enough i.
  apply: (@lt_crealP _ 1 i i) => //=; rewrite ler_add2r.
  apply: le_trans (uboundP x i); exact: ler_norm.
by close.
Qed.

Lemma ltcr_le_trans (y x z : creal F): (x < y -> y <= z -> x < z)%CR.
Proof.
move=> ltxy leyz; pose_big_enough i.
  have hpos : 0 < diff ltxy / 2%:~R.
    apply: divr_gt0; rewrite ?ltr0Sn //; exact: diff_gt0.
  apply: (@lt_crealP _  ((diff ltxy) / 2%:~R) i i) => //=.
  have -> : x i + diff ltxy / 2%:~R = x i + diff ltxy - diff ltxy / 2%:~R.
    apply/eqP; rewrite eq_sym subr_eq -addrA -mulrDr.
    have <- : 1 = 2%:~R^-1 + 2%:~R^-1 :> F by rewrite [LHS](splitf 2) div1r.
    by rewrite mulr1.
  rewrite ler_subl_addr; apply: le_trans (diffP _ _) _ => //; apply: ltW.
  by apply: le_modP.
by close.
Qed.

Lemma lecr_lt_trans (y x z : creal F): (x <= y)%CR -> (y < z)%CR -> (x < z)%CR.
Proof.
(* We could just use the opposites but we do not have the lemmas... *)
(* Hence we copy paste mutatis mutandis the previous proof *)
move=> lexy ltyz; pose_big_enough i.
  have hpos : 0 < diff ltyz / 2%:~R.
    apply: divr_gt0; rewrite ?ltr0Sn //; exact: diff_gt0.
  apply: (@lt_crealP _  ((diff ltyz) / 2%:~R) i i) => //=.
  apply: le_trans (@diffP _ _ _ ltyz _ _ _) => //; rewrite -ler_subr_addr.
  suff <- : y i + diff ltyz / 2%:~R = y i + diff ltyz - diff ltyz / 2%:~R.
    by apply: ltW; apply: le_modP.
  apply/eqP; rewrite eq_sym subr_eq -addrA -mulrDr.
  have <- : 1 = 2%:~R^-1 + 2%:~R^-1 :> F by rewrite [LHS](splitf 2) div1r.
  by rewrite mulr1. 
by close.
Qed.

Lemma lecr_trans (y x z : creal F): (x <= y -> y <= z -> x <= z)%CR.
Proof.
move=> lexy leyz ltzx; apply: (@eq_creal_refl _ z); apply: lt_creal_neq.
by apply: ltcr_le_trans leyz; apply: ltcr_le_trans lexy.
Qed.

Lemma lecr_mulf2r (z : F) (x y : creal F) : 
  (x <= y)%CR ->  0 <= z -> (x * z%:CR <= y * z%:CR)%CR.
Proof.
move=> lexy.
rewrite le_eqVlt; case/orP=> [/eqP <- | lt0z]; first by rewrite !mul_creal0.
move => h; apply: lexy.
have aux t : (t == t * z%:CR * z^-1%:CR)%CR.
  rewrite -mulcrA -cst_crealM mulfV ?mul_creal1 //; move: lt0z; rewrite lt0r.
  by case/andP.
rewrite [x]aux {}[y]aux; apply: ltcr_mul2r => //; apply/lt_creal_cst.
by rewrite invr_gt0.
Qed.


Lemma lecr_mulf2l (z : F) (x y : creal F) : (x <= y)%CR ->  
  0 <= z -> (z%:CR * x <= z%:CR * y)%CR.
Proof. by rewrite ![(z%:CR * _)%CR]mulcrC; apply: lecr_mulf2r. Qed.

Lemma lecr_lt_add (x y z t : creal F) : (x <= y -> z < t -> x + z < y + t)%CR.
Proof. 
move=> lxy lzt; apply: (@lecr_lt_trans (y + z)%CR); last exact: ltcr_add2l.
move/(ltcr_add2l (-z)%CR)=> abs; apply: lxy; move: abs.
by rewrite ![(- z + _)%CR]addcrC -!addcrA addcrN !add_creal0.
Qed.

Lemma ltcr_le_add (x y z t : creal F) : (x < y -> z <= t -> x + z < y + t)%CR.
Proof.
move=> *; rewrite [X in (X < _)%CR]addcrC [X in (_ < X)%CR]addcrC. 
by apply: lecr_lt_add. 
Qed.

Lemma ltcr_spaddl (y x z : creal F) : (0 < x -> y <= z -> y < x + z)%CR.
Proof. move=> *; rewrite -[y]add_0creal; exact: ltcr_le_add. Qed.

Lemma ltcr_spaddr (y x z : creal F) : (0 < x -> y <= z -> y < z + x)%CR.
Proof. move=> *; rewrite -[y]add_creal0; exact: lecr_lt_add. Qed.

Lemma asympt_eq_creal (x : creal F) (y : nat -> F) :
  {asympt e : i / `|x i - y i| < e} ->  creal_axiom y.
Proof.
case: x => x [mx mxP]; case=> M MP; 
exists_big_modulus m F.
  move=> eps i j lt_eps_0 hmi hmj; pose d (k : nat) := x k - y k.
  have -> : y i - y j = d j + (x i - x j) - d i.
    rewrite /d [(_ - _) + _]addrC addrA addrNK opprB addrA [_ - x i]addrC.
    by rewrite addrA addKr addrC.
  suff step1 : `|d j + (x i - x j)| + `|d i| < eps.
    by apply: le_lt_trans step1; rewrite -[`|d i|]normrN; apply: ler_norm_add.
  suff step2 : `|d j| + `|x i - x j| + `|d i| < eps.
    by apply: le_lt_trans step2; rewrite ler_add2r; apply: ler_norm_add.
  have -> : eps = eps / 3%:~R + eps / 3%:~R + eps / 3%:~R.
    rewrite /= in eps lt_eps_0 hmi hmj *.
    rewrite -!mulrDl -[in X in _ = X](mulr1 eps) -!mulrDr -mulrA.
    suff -> : (1 + 1 + 1) / 3%:~R = 1 :> F by rewrite mulr1.
    rewrite -[X in (X + X + X) / _ = _]/(1%:~R) -!rmorphD /= mulfV //.
    by rewrite intr_eq0.
  have heps : 0 < eps / 3%:~R by apply: divr_gt0 => //; rewrite ltr0z.
  apply: ltr_add => //; last exact: MP.
  apply: ltr_add=> //; first by exact: MP.
  by move=> {MP}; apply: mxP.
by close.
Qed.

End ExtraCreals.
