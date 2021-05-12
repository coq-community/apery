From mathcomp Require Import all_ssreflect all_algebra.

From mathcomp Require Import bigenough cauchyreals.

Require Import bigopz extra_cauchyreals extra_mathcomp.
Require Import field_tactics shift.

Require Import seq_defs.
Require Import arithmetics.
Require Import c_props s_props z3seq_props a_props b_props b_over_a_props.

Require hanson.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory BigEnough.

Open Scope ring_scope.

(******************************************************************************)
(* In this file we define the real number zeta(3) and prove that it is        *)
(* irrational. This is a constructive proof which is essentially based on the *)
(* two following 'informal' proofs:                                           *)
(* - A proof that Euler missed, an informal report, A. van der Poorten,       *)
(*   Mathematical Intelligencer, vol 1 (1979), pp 195-203                     *)
(* - An Algolib-aided Version of Apery's Proof of the Irrationality of        *)
(*   zeta(3) Bruno Salvy, 2003, Maple worksheet available online at           *)
(*   http://algo.inria.fr/libraries/autocomb/Apery2-html/apery1.html          *)
(* We however had to make explicit or more elementary some parts of the proof *)
(* to complete the formalization, see the comments below.                     *)
(* For the time being, the proof still relies on a result we did not          *)
(* formalize about the asymptotic behaviour of the sequence lcm(1,...,n).     *)
(******************************************************************************)


Ltac raise_big_enough := solve [big_enough_trans].


(* We prove that z3seq is a Cauchy sequence. *)
Lemma creal_z3seq : creal_axiom z3seq.
Proof.
rewrite /creal_axiom.
pose n_inv_seq (n : nat) := n%:~R^-1 : rat.
have [/= modulus_n_inv modulus_n_inv_P] : {asympt e : i / n_inv_seq i < e}.
  exists_big_modulus M rat => /=.
    move=> eps i lt_eps0 hMi.
    rewrite /n_inv_seq -div1r ltr_pdivr_mulr;
      last by rewrite ltr0n; raise_big_enough.
    rewrite -ltr_pdivr_mull // mulr1.
    apply: (lt_trans (archi_boundP _) _); first by rewrite ger0E ltW.
    rewrite ltr_nat; raise_big_enough.
  by close.
exists_big_modulus m rat.
  move=> eps i j lt_eps_0 hmi hmj.
  wlog ltij : i j hmi  hmj / (j < i)%N.
    move=> hwlog; case: (ltngtP i j); last by move ->; rewrite subrr.
    - rewrite distrC; exact/hwlog.
    - exact/hwlog.
  rewrite gtr0_norm; last exact: lt_0_Dz3seq.
  pose v (n : nat) :=  (n%:~R ^ 2) ^-1 : rat.
  have vpos (n : nat) : (0 < n)%N -> 0 < v n.
    by move=> ?; rewrite /v invr_gt0; apply: exprz_gt0; rewrite ltr0n.
  have maj : z3seq i - z3seq j <=
             - 2%:~R^-1 * \sum_(j <= k < i) (v (k + 1)%N - v k).
    rewrite Dz3seqE // big_add1 /= mulr_sumr.
    rewrite [X in X <= _]big_nat [X in _ <= X]big_nat.
    apply: ler_sum => k; case/andP=> hjk hki; rewrite /v addn1.
    apply: z3seq_smd_maj; rewrite ltr0n; apply: leq_trans _ hjk.
    raise_big_enough.
  apply: (le_lt_trans maj) => {maj}; rewrite telescope_nat //.
  suff maj : v j < 2%:~R * eps.
    rewrite mulNr -mulrN opprB ltr_pdivr_mull // ltr_subl_addr.
    apply: (lt_trans maj); rewrite ltr_addl; apply: vpos; exact: ltn_trans ltij.
  have maj : v j < j%:~R ^-1.
    rewrite /v -div1r ltr_pdivr_mulr; last by rewrite exprz_gt0 // ltr0n.
    by rewrite mulKf ?ltr1n // lt0r_neq0 // ltr0n.
  by apply: (lt_trans maj); apply: modulus_n_inv_P => //; rewrite pmulr_rgt0.
by close.
Qed.


(* Actual definition of \zeta(3) as a Cauchy real, i.e. the equivalence class *)
(* of the sequence z3seq for Cauchy equivalence. *)
Definition z3 : creal rat_realFieldType := CReal creal_z3seq.

(* We prove that the sequences z3seq and b / a are asymptotically close. *)
Lemma z3seq_b_over_a_asympt : {asympt e : i / `|z3seq i - b_over_a_seq i| < e}.
Proof.
exists_big_modulus M rat.
  move=> eps i peps hmi /=.
  suff step1 : \sum_(0 <= i0 < Posz i + 1 :> int) `|c i i0 * s i i0| < eps * a i.
    suff -> : b_over_a_seq i =
              z3seq i + (\sum_(0 <= k < Posz i + 1 :> int) c i k * s i k) / a i.
      rewrite opprD addNKr normrN normrM normfV.
      rewrite [X in _ / X](gtr0_norm (lt_0_a _)) // ltr_pdivr_mulr ?lt_0_a //.
      exact: le_lt_trans (ler_norm_sum _ _ _) _.
    have -> : b_over_a_seq i = (\sum_(0 <= k < Posz i + 1 :> int)
                                (c i k * ghn3 i + c i k * s i k)) / a i.
      rewrite /b_over_a_seq; congr (_ / a i); apply: eq_bigr => j _.
      by rewrite /v /u mulrDr.
    rewrite big_split /= mulrDl; congr (_ + _); rewrite -mulr_suml mulrAC.
    rewrite mulfV ?mul1r //; exact: a_neq0.
  rewrite -PoszD !eq_big_int_nat /=.
  have step2 (i0 : nat) : (0 <= i0 <= i)%N ->
    `|c i i0 * s i i0| <= c i i0 * i0%:~R / (2%:~R * (Posz i)%:~R ^ 2).
    case/andP=> _ hi0; rewrite normrM [`|c i i0|]gtr0_norm ?lt_0_c //.
    rewrite -mulrA ler_pmul2l //; last exact: lt_0_c.
    apply: s_maj => //; rewrite ltr0n; raise_big_enough.
  apply: (@le_lt_trans _ _ (\sum_(0 <= i0 < i + 1)
                   c i i0 * i0%:~R / (2%:~R * i%:~R ^ 2))).
    rewrite [X in X <= _]big_nat [X in _ <= X]big_nat.
    apply: ler_sum => j; case/andP=> h0j.
    rewrite addn1 ltnS => hji; exact: step2.
  apply:(@le_lt_trans _ _ ((\sum_(0 <= i0 < i + 1) c i i0) / (2%:~R * i%:~R))).
    rewrite [X in X <= _]big_nat [in X in _ <= X]big_nat.
    rewrite mulr_suml; apply: ler_sum => j; case/andP=> h0j.
    rewrite addn1 ltnS => hji; rewrite -mulrA ler_pmul2l ?lt_0_c //.
    rewrite mulrA invfM mulrCA ger_pmulr; last by rewrite gtr0E mulr_gt0 ?ltr0n.
    by rewrite ler_pdivr_mulr ?ltr0n // mul1r ler_nat.
  rewrite mulrC -eq_big_int_nat /= ltr_pmul2r; last first.
    rewrite -/(a i); exact: lt_0_a.
  rewrite -div1r ltr_pdivr_mulr; last by apply: mulr_gt0; rewrite ltr0n.
  rewrite mulrA mulrC -ltr_pdivr_mulr; last by apply: mulr_gt0.
  apply: lt_trans (archi_boundP _) _; last by rewrite ltr_nat; raise_big_enough.
  by rewrite mulr_ge0 // invr_ge0 mulr_ge0 // ltW.
by close.
Qed.

(* As a corollary, b_over_a itself is also a Cauchy sequence. *)
Corollary creal_b_over_a_seq : creal_axiom b_over_a_seq.
Proof. apply: (@asympt_eq_creal _ z3); exact: z3seq_b_over_a_asympt. Qed.

(* We define the Cauchy real b_over_a, i.e. the equivalent class *)
(* of the sequence b / a for Cauchy equivalence. *)
Definition b_over_a := CReal creal_b_over_a_seq.

(* Obviously, z3 and b_over_a are the same Cauchy real. *)
Fact z3_eq_b_over_a : (z3 == b_over_a)%CR.
Proof. apply: eq_crealP. exact: z3seq_b_over_a_asympt. Qed.


(* Using the properties of the Casoratian of a and b, we establish the *)
(* positivity of zeta3 - b n / an. *)
Lemma lt0_z3_minus_b_over_a (n : nat) :
  (2 <= n)%N -> (0%:CR < z3 - (b_over_a_seq n)%:CR)%CR.
Proof.
move=> le2n.
pose_big_enough m.
  have diff_pos1 (k l : nat) : (k < l)%N -> (1 < k)%N ->
                               0 < b_over_a_seq l - b_over_a_seq k.
    move=> ltkn lt1k; rewrite Db_over_a_casoratian //.
    rewrite (big_cat_nat _ _ _ (leqnSn _) ltkn) big_nat1 /=.
    have aux (i : nat) :
      0 < 6%:~R / (i%:~R + 1%:~R) ^ 3 / (a (int.shift 1 i) * a i).
      apply: divr_gt0; first by apply: lt_0_ba_casoratian.
      apply:mulr_gt0; exact: lt_0_a.
    apply: ltr_spaddl => //;  apply: sumr_ge0 => i _; exact: ltW.
  suff diff_pos2 : (0 <= b_over_a - (b_over_a_seq m)%:CR)%CR.
    have ->: b_over_a_seq n = b_over_a_seq m + (b_over_a_seq n - b_over_a_seq m).
      by rewrite addrCA subrr addr0.
    have -> : (z3 - (b_over_a_seq m + (b_over_a_seq n - b_over_a_seq m))%:CR ==
           z3 - (b_over_a_seq m)%:CR + (b_over_a_seq m - b_over_a_seq n)%:CR)%CR.
      by apply: eq_creal_ext=> i /=; rewrite -addrA opprD opprB.
    rewrite z3_eq_b_over_a; apply: ltcr_spaddr=> //; apply: lt_creal_cst.
    apply: diff_pos1; raise_big_enough.
  apply: (@le_crealP _ m.+1) => *; apply: ltW.
  apply: diff_pos1; raise_big_enough.
by close.
Qed.

(* Again using the properties of the casoratian, we can prove that *)
(* delta n := a(n)zeta3(n) - b(n) is dominated by O(1 / a(n)^2). An easy   *)
(* constant is (a "nearby" rational number equal or greater than) 6 * zeta(3).*)
Definition Kdelta := ubound (6%:~R%:CR * z3)%CR.

(* Later in the study of sequence sigma we'll need the fact that this constant *)
(* is non zero. *)
Fact lt_0_Kdelta : 0 < Kdelta.
Proof. by rewrite /Kdelta; exact: ubound_gt0. Qed.

Lemma delta_asympt : {large : nat | forall n, (large <= n)%N ->
     ((a n)%:CR * z3 - (b n)%:CR <= (Kdelta * (1 / a n))%:CR)%CR}.
Proof.
pose_big_enough large.
exists large => n hlarge.
  suff step1 i : (n <= i)%N ->
                 a n * b_over_a_seq i - b n <= 6%:~R * z3seq i * (1 / a n).
    apply: (@lecr_trans  _ (6%:~R%:CR * z3 * (1 / a n)%:CR))%CR; last first.
      rewrite cst_crealM; apply: lecr_mulf2r; first by apply: le_ubound.
      apply: divr_ge0=> //; apply: ltW; exact: lt_0_a.
    rewrite {1}z3_eq_b_over_a; apply: (@le_crealP _ n) => j hj //=; exact: step1.
  move=> leni.
  suff step2 : b_over_a_seq i - b_over_a_seq n <= 6%:~R * z3seq i / a n ^ 2.
    have lt_0_anV : 0 < (1 / a n) by apply: divr_gt0 => //; apply: lt_0_a.
    have an_neq0 : a n != 0 by apply: lt0r_neq0; apply: lt_0_a.
    rewrite -(ler_pmul2r lt_0_anV) mulrDl mulrAC div1r mulfV // mul1r mulNr.
    by set z := (X in _ <= X / _ / _); rewrite -mulrA -invrM.
  have step3 : b_over_a_seq i - b_over_a_seq n <=
               (\sum_(n <= k < i) 6%:~R / (k%:~R + 1%:~R) ^ 3) / a n ^ 2.
    rewrite Db_over_a_casoratian; [ | raise_big_enough | exact: leni].
    rewrite [X in X <= _]big_nat_cond [in X in _ <= X]big_nat_cond.
    rewrite mulr_suml; apply: ler_sum => j; rewrite andbT; case/andP=> hnj hji.
    have lt0j : (0 < j)%N by apply: leq_trans hnj; raise_big_enough.
    rewrite ler_pmul2l ; last exact: lt_0_ba_casoratian.
    rewrite exprSz expr1z lef_pinv; [| (apply: mulr_gt0; exact: lt_0_a)..].
    apply: ler_pmul; rewrite ?(ltW (lt_0_a _)) //; apply: a_incr => //.
    by rewrite int.shift2Z lez_nat; apply: leq_trans hnj _; rewrite addn1.
  apply: le_trans step3 _; rewrite ler_pmul2r; last by rewrite !gtr0E // lt_0_a.
  rewrite -mulr_sumr ler_pmul2l //; set lhs := (X in X <= _).
  have {lhs} -> : lhs =   \sum_(n.+1 <= i0 < i.+1) (i0%:~R ^ 3)^-1.
    rewrite {}/lhs big_add1 /=; apply: eq_bigr => k _.
    by rewrite -[k.+1]addn1 PoszD rmorphD /=.
  rewrite z3seqE; have leSnSi : (n.+1 <= i.+1)%N by [].
  rewrite [in X in _ <= X](big_cat_nat _ _ _ _ leSnSi) //= ler_addr.
  rewrite big_nat_cond; apply: sumr_ge0 => k; rewrite andbT.
  by case/andP=> lt0k lekn; rewrite ger0E; apply: exprz_ge0; rewrite ler0z.
by close.
Qed.

Definition Ndelta := projT1 delta_asympt.

Fact NdeltaP (n : nat) : (Ndelta <= n)%N ->
     ((a n)%:CR * z3 - (b n)%:CR <= (Kdelta * (1 / a n))%:CR)%CR.
Proof. by rewrite /Ndelta; case: delta_asympt => /= ?; exact. Qed.


(* We define an a priori real valued sequence whose properties forbid *)
(* zeta(3) to be irrational. ***)

Local Notation l := iter_lcmn.

Definition sigma (n : nat) :=
  (2%:~R%:CR * ((l n)%:~R ^ 3)%:CR * ((a n)%:CR * z3 - (b n)%:CR))%CR.

(* Sequence sigma has positive terms. *)
Lemma lt_0_sigma (n : nat) : (2 <= n)%N -> (0%CR < sigma n)%CR.
Proof.
move=> le2n.
suff h : (0 < (a n)%:CR * z3 - (b n)%:CR)%CR.
  rewrite /sigma; apply: mulr_gtcr0 => //; rewrite -cst_crealM.
  by apply/lt_creal_cst; apply: mulr_gt0 => //; rewrite !gtr0E // iter_lcmn_gt0.
suff : (0 < (a n)%:CR * (z3 - (b_over_a_seq n)%:CR))%CR.
  by rewrite mulcrDr mulcrN -cst_crealM mulrC mulfVK // a_neq0.
apply: mulr_gtcr0; last exact: lt0_z3_minus_b_over_a.
by apply: lt_creal_cst; apply: lt_0_a.
Qed.

(* This is the *statement* of the result we use without a formal *)
(* proof. It is a weak corollary of the Prime Number Theorem (pnt) but *)
(* can be obtained directly from more elementary means, see a proof in *)
(* "On the product of the primes" D. Hanson, *)
(* Canad. Math. Bull. Vol. 15(1), 1972. *)
(* A close inspection of the paper validates in particular the *)
(* hypothesis we need on K2^3. *)

(* Definition weak_pnt := exists K2 : rat, exists K3 : rat, exists N : nat, *)
(*   [/\ 0 < K2, *)
(*       0 < K3, *)
(*       K2 ^ 3 < 33%:~R & *)
(*       forall n : nat, (N <= n)%N ->  (l n)%:~R < K3 * K2 ^ n]. *)

(* In the following two sections, we work in a context which assumes *)
(* that property weak_pnt holds. *)
Section SigmaGoesToZero.

Lemma hanson : exists K2 : rat, exists K3 : rat, exists N : nat,
  [/\ 0 < K2,
      0 < K3,
      K2 ^ 3 < 33%:~R &
      forall n : nat, (N <= n)%N ->  (l n)%:~R < K3 * K2 ^ n].
Proof.
exists 3%:Q.
case: hanson.Hanson.t3 => K [Hpos H].
exists (K.+1)%:Q; exists 0%nat.
split.
- by rewrite ltr0n.
- by rewrite ltr0n.
- by rewrite -exprnP -natrX ltr_nat.
- move => n _. apply: le_lt_trans (H n) _.
  by rewrite -exprnP -natrX -natrM ltr_nat ltn_mul2r expn_gt0 /=. (* funny: does not work without the /= *)
Qed.

Lemma sigma_goes_to_0 (eps : rat) : 0 < eps ->
  exists M : nat, forall n : nat, (M <= n)%N -> (sigma n < eps%:CR)%CR.
Proof.
move=> eps_pos.
have [K2 [K3 [large [K2pos K3pos K2_maj hanson]]]] := hanson.
pose C := 2%:~R * (K3 ^ 3) * Kdelta * Ka ^-1.
have Cpos : 0 < C.
  rewrite /C pmulr_rgt0; first by rewrite invr_gt0; exact: lt_0_Ka.
  rewrite pmulr_rgt0; first exact: lt_0_Kdelta.
  apply: mulr_gt0; [by [] | by apply: exprz_gt0].
have heps : 0 < eps / C by apply: divr_gt0.
have hr : 0 < K2 ^ 3 / 33%:~R < 1.
  by rewrite andbC -ltr_pdivl_mulr // invrK mul1r K2_maj divr_gt0 // exprn_gt0.
have [N hN] := Gseqlt1 heps hr.
pose_big_enough M.
  exists M => n hn.
  have aux : (sigma n <
         (2%:~R * (K3 * K2 ^ n) ^ 3 *  Kdelta *  Ka^-1 / 33%:~R ^ n)%:CR)%CR.
    rewrite /sigma -mulcrA -3!mulrA [in X in (_ < X)%CR]cst_crealM.
    apply: ltcr_mul2l; last by apply/lt_creal_cst.
    have Dn_pos : 0 < (l n)%:~R :> rat.
      rewrite -[0]/(0%:~R) ltr_nat iter_lcmn_gt0; raise_big_enough.
    rewrite [in X in (_ < X)%CR]cst_crealM.
    apply: ltcr_pmul; first by apply/lt_creal_cst; apply: exprn_gt0.
    - apply/lt_creal_cst; apply: mulr_gt0; first exact: lt_0_Kdelta.
      apply: divr_gt0; last by apply: exprn_gt0; rewrite ltr0n.
      rewrite invr_gt0; exact: lt_0_Ka.
    - apply/lt_creal_cst; rewrite ltr_expn2r //; first exact: ltW.
      apply: hanson; raise_big_enough.
    - apply: lecr_lt_trans (NdeltaP _) _; first by raise_big_enough.
      apply/lt_creal_cst; rewrite ltr_pmul2l; last exact: lt_0_Kdelta.
      apply: a_asympt; raise_big_enough.
  apply: lt_creal_trans aux _; apply/lt_creal_cst; set lhs := (X in (X < _)).
  have -> : lhs = C * (K2 ^ 3 / 33%:~R) ^ n.
    (* what an ugly script... rat_field is bad with _ ^ n *)
    rewrite {}/lhs /C expfzMl [(_ / _) ^ n]expfzMl.
    have h : 33%:~R^-1 ^ n = (33%:~R ^ n) ^-1 :> rat by rewrite -exprnP -exprVn.
    rewrite {}[X in _ = _ * _ * _ * (_ * X)]h exprzAC.
    set x := _ ^ n;  set y := _ ^ _ n; rat_field.
    split; first by apply/eqP; apply: expfz_neq0; rewrite intr_eq0.
    apply/eqP; apply: lt0r_neq0; exact: lt_0_Ka.
  rewrite -ltr_pdivl_mull -[X in _ < X]mulrC; last by rewrite mulrC; exact: Cpos.
  apply: hN; raise_big_enough.
by close.
Qed.

End  SigmaGoesToZero.

Section AperyConstantIsIrrational.

(* Finally, the irrationality proof of zeta(3). We do not use the standard *)
(* irrationality criterium using the denominator scale, but rather a *)
(* simpler argument based on iter_lcmn_mul_rat that works in our case. *)
Theorem zeta_3_irrational : ~ exists (r : rat), (z3 == r%:CR)%CR.
Proof.
case=> z3_rat z3_ratP; case: (denqP z3_rat) z3_ratP => d dP z3_ratP.
have heps : 0 < 1 / 2%:~R :> rat by [].
have [M MP] := sigma_goes_to_0 heps.
pose sigma_Q (n : nat) : rat := 2%:~R * (l n)%:~R ^ 3 * (a n * z3_rat - b n).
have sigma_QP (n : nat) : ((sigma_Q n)%:CR == sigma n)%CR.
  by rewrite /sigma z3_ratP -!cst_crealM -cst_crealB -cst_crealM.
pose_big_enough n.
  have h_pos : 0 < sigma_Q n.
    apply/lt_creal_cst; rewrite sigma_QP; apply: lt_0_sigma; raise_big_enough.
  have h_lt1 : sigma_Q n < 1 / 2%:~R.
    apply/lt_creal_cst; rewrite sigma_QP; apply: MP; raise_big_enough.
  suff : 1 <= sigma_Q n by apply/negP; rewrite -ltNge; apply: lt_trans h_lt1 _.
  suff /QintP [z zP] : sigma_Q n \is a Qint.
    by move: h_pos; rewrite zP ler1z -gtz0_ge1 ltr0z; apply.
  suff hr : 2%:~R * (l n)%:~R ^ 3 * (a n * z3_rat) \is a Qint.
    rewrite /sigma_Q mulrDr mulrN; apply: rpredD; first exact: hr.
    rewrite rpredN; apply: Qint_l3b.
  have Qint_lz3 : (l n)%:~R * z3_rat \is a Qint.
    apply: iter_lcmn_mul_rat; rewrite normr_denq dP lez_nat; raise_big_enough.
  have -> : 2%:~R * (l n)%:~R ^ 3 * (a n * z3_rat) =
            ((l n)%:~R * z3_rat) * (2%:~R * (l n)%:~R ^ 2 * a n) by rat_field.
  apply: rpredM; [exact: Qint_lz3|]; apply: rpredM; [|exact: Qint_a].
  apply: rpredM; [|apply: rpredX]; exact: rpred_int.
by close.
Qed.

End AperyConstantIsIrrational.

About zeta_3_irrational.
 (* Time *) Print Assumptions zeta_3_irrational.
