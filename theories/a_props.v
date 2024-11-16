Require Import BinInt.

From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint rat archimedean.
From mathcomp Require Import realalg.

From CoqEAL Require Import hrel param refinements.
From CoqEAL Require Import pos binnat binint rational.
Import Refinements (* AlgOp *).

Require Import tactics shift binomialz bigopz rat_of_Z rho_computations.
Require annotated_recs_c.
Require Import seq_defs c_props initial_conds algo_closures.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.


(**** Properties the sequence a  ****)




(* Although the type of the values of a is the one of rationals, these *)
(* values are all integer. *)
Fact Qint_a (i : int)  : a i \is a Num.int.
Proof. by apply: rpred_sum => ?; rewrite rpred_zify. Qed.

(* The values of a are strictly positive at positive indexes. *)
Fact lt_0_a (k : int) : 0 <= k -> 0 < a k.
Proof.
move=> h0k; rewrite /a big_int_recl /=; last lia.
apply: ltr_wpDr; last exact: lt_0_c.
by rewrite big_int_cond sumr_ge0 => // i ?; apply/ltW/lt_0_c; lia.
Qed.

(* The values of a are nonnegative *)
Fact le_0_a (k : int) : 0 <= a k.
Proof. rewrite /a big_int_cond sumr_ge0 => // i ?; apply/ltW/lt_0_c; lia. Qed.

Fact a_neq0 (k : int) : 0 <= k -> a k != 0.
Proof. by move/lt_0_a; rewrite lt0r; case/andP. Qed.

(* a is increasing *)
Fact a_incr (n m : int) : n <= m -> a n <= a m.
Proof.
move=> lenm.
have [le0n | ltn0] := lerP 0 n; last by rewrite {1}/a big_geqz ?le_0_a; lia.
have leSnSm : n + 1 <= m + 1 by lia.
rewrite /a (big_cat_int _ _ _ _ leSnSm) //=; apply: ler_wpDr=> //; last first.
  rewrite [X in X <= _]big_int_cond [X in _ <= X]big_int_cond /=.
  apply: ler_sum => i; rewrite andbT => /andP [hi hin]; apply: c_incr; lia.
rewrite big_int_cond; apply: sumr_ge0 => i; rewrite andbT => /andP [hni hmi].
by apply/ltW/lt_0_c; lia.
Qed.

(*  One of the important properties of a for the proof is the asymptotic     *)
(*  behaviour, namely that a dominates 33 ^ n. We diverge from standard      *)
(* presentations by formalizing an elementary proof, based on the            *)
(*  monotonicity of the successive quotients  a (n + 1) / a n.               *)

(* We define rho the auxiliary sequence of quotients of consecutive values   *)
(* of a *)
Definition rho (i : int) : rat := a (i + 1) / a i.


(* a3_eq and a2_eq should use rat_of_positive *)
Lemma rho2_eq : rho 2 = rat_of_Z 1445 / rat_of_Z 73.
Proof. by rewrite /rho a3_eq a2_eq. Qed.

Fact le_1_rho (i : int) : 0 <= i -> 1 <= rho i.
Proof.
move=> lei0; rewrite /rho ler_pdivlMr; last exact: lt_0_a.
by rewrite mul1r; apply: a_incr; rewrite ler_wpDr.
Qed.

Fact lt_0_rho (i : int) : 0 <= i -> 0 < rho i.
Proof. by move=> lei0; apply/divr_gt0/lt_0_a/lei0/lt_0_a/addr_ge0. Qed.

(* The monotonicity of rho is a consequence of a being solution of Apéry's *)
(* recurrence. We introducte short names for its (fraction) coefficients   *)

(* Let alpha (i : int) := annotated_recs_c.P_cf1 i / annotated_recs_c.P_cf2 i. *)
(* Let beta (i : int) := annotated_recs_c.P_cf0 i / annotated_recs_c.P_cf2 i. *)


(* TODO : FIX/MOVE *)



Definition beta (x : rat) : rat := ((x + rat_of_Z 1) / (x + rat_of_Z 2)) ^+ 3.

(* END TODO *)

Fact lt_0_beta (x : rat) : 0 <= x -> 0 < beta x.
Proof. by move=> le0i; apply/exprn_gt0/divr_gt0; apply/ltr_wpDl. Qed.

Fact lt_beta_1 (x : rat) : 0 <= x -> beta x < 1.
Proof.
move=> le0i; rewrite /beta expr_lte1 //; last by apply/divr_ge0; apply/addr_ge0.
by rewrite ltr_pdivrMr ?ltr_wpDl // mul1r ltrD2l lt_rat_of_Z.
Qed.

(* TODO : FIX/MOVE *)

Definition alpha (x : rat) :=
  (rat_of_Z 17 * x ^+ 2 + rat_of_Z 51 * x + rat_of_Z 39) *
  (rat_of_Z 2 * x + rat_of_Z 3) / (x + rat_of_Z 2) ^+ 3.


Fact lt_2_alphaN (x : rat) : 0 <= x ->  rat_of_Z 2 < alpha x.
Proof.
move=> le0i; rewrite /alpha.
have npos : 0 < x + rat_of_Z 2 by apply: ltr_wpDl; rewrite ?ler0z.
rewrite ltr_pdivlMr; last by apply: exprn_gt0.
have trans: rat_of_Z 2 * (x + rat_of_Z 2) ^+ 3 <=
            rat_of_Z 2 * (x + rat_of_Z 2) ^+ 2 * (rat_of_Z 2 * x + rat_of_Z 3).
  rewrite [_ ^+ 3]exprSr mulrA ler_wpM2l //.
    by rewrite mulr_ge0 // exprn_ge0 // addr_ge0.
  by apply: lerD (ler_peMl _ _) _ => //; ring_lia.
apply: le_lt_trans trans _.
suff trans : rat_of_Z 2 * (x + rat_of_Z 2) ^+ 2 <
             rat_of_Z 17 * x ^ 2 + rat_of_Z 51 * x + rat_of_Z 39.
  by rewrite ltr_pM2r // ltr_wpDl // mulr_ge0.
rewrite -exprnP sqrrD !mulrDr; apply: ler_ltD; last first.
  by rewrite [_ < _]refines_eq.
apply: lerD; first by rewrite ler_wpM2r ?exprn_ge0 // [_ <= _]refines_eq.
by rewrite [x * _]mulrC mulrA -mulrDl ler_wpM2r // [_ <= _]refines_eq.
Qed.


Fact lt_0_alpha (x : rat) : 0 <= x -> 0 < alpha x.
Proof. by move=> le0i; apply/lt_trans/lt_2_alphaN/le0i. Qed.

(* A Maple aided proof that - alpha is increasing. *)
Fact alpha_incr (x : rat) : 0 <= x -> alpha x <= alpha (x + 1).
Proof.
move=> le0i; rewrite -subr_ge0; set rhs := (X in 0 <= X).
have -> : rhs = (rat_of_Z 51 * x ^+ 4 + rat_of_Z 456 * x ^+ 3 +
                 rat_of_Z 1497 * x ^+ 2 + rat_of_Z 2136 * x + rat_of_Z 1121) /
                ((x + rat_of_Z 3) ^+ 3 * (x + rat_of_Z 2) ^+ 3).
  by rewrite /rhs /alpha; field; rewrite !lt0r_neq0 // ltr_wpDl.
by rewrite divr_ge0 ?addr_ge0 // mulr_ge0 // exprn_ge0 // addr_ge0.
Qed.

(* delta is the discriminant *)
Local Definition delta (x : rat) := alpha x ^+ 2 - rat_of_Z 4 * beta x.

Fact lt_0_delta (x : rat) : 0 <= x -> 0 < delta x.
Proof.
move=> le0x; rewrite /delta subr_gt0.
have /lt_trans -> //: rat_of_Z 4 * beta x < rat_of_Z 4.
  by rewrite gtr_pMr // lt_beta_1.
have -> : rat_of_Z 4 = rat_of_Z 2 ^+ 2 by ring.
rewrite -subr_gt0 subr_sqr mulr_gt0 //.
  rewrite subr_gt0; exact: lt_2_alphaN.
by rewrite addr_gt0 ?lt_0_alpha.
Qed.

(* Maple aided proof again that delta is increasing *)
Lemma delta_incr (x : rat) : 0 <= x -> delta x <= delta (x + 1).
Proof.
move=> le0x; rewrite -subr_ge0; set rhs := (X in 0 <= X).
have -> : rhs = (rat_of_Z 3456 * x ^ 10 + rat_of_Z 77550 * x ^  9 +
                 rat_of_Z 777825 * x ^ 8 + rat_of_Z 4591644 * x ^ 7 +
                 rat_of_Z 17666100 * x ^ 6 + rat_of_Z 46291464 * x ^ 5 +
                 rat_of_Z 83678475 * x ^ 4 + rat_of_Z 103061566 * x ^ 3 +
                 rat_of_Z 82798770 * x ^ 2 + rat_of_Z 39197496 * x +
                 rat_of_Z 8307151) /
                ((x + rat_of_Z 3) ^ 6 * (x + rat_of_Z 2) ^ 6).
  rewrite {}/rhs /delta /alpha /beta.
  by field; rewrite !lt0r_neq0 // ltr_wpDl.
by rewrite divr_ge0 ?addr_ge0 // mulr_ge0 // exprn_ge0 // addr_ge0.
Qed.



(* (* The proof goes by studying the following homographic transformation. *) *)
Lemma hE (x y : rat) : h x y = alpha x - beta x / y.
Proof. by []. Qed.

(* Here the rat_field is used to prove a simple reorganisation of terms. *)
Lemma rho_rec (i : int) : Posz 2 <= i -> rho (i + 1) = h i%:Q (rho i).
Proof.
move=> le2i; rewrite hE.
have rhoi_neq0 : rho i != 0 by apply/lt0r_neq0/lt_0_rho/le_trans/le2i.
have ai_neq0 : a i != 0 by apply/a_neq0/le_trans/le2i.
rewrite -[alpha i%:Q](mulfK rhoi_neq0) -mulrBl; apply: canRL (mulfK _) _ => //.
have -> : rho (i + 1) * rho i = a (i + 2) / a i.
  by rewrite /rho mulrA mulfVK -?addrA //; apply/a_neq0; lia.
apply: canLR (mulfK _) _; rewrite // mulrDl -mulrA mulNr /rho divfK //.
have c2_neq0 : annotated_recs_c.P_cf2 i != 0.
  by rewrite /annotated_recs_c.P_cf2 lt0r_neq0 ?exprn_gt0 ?addr_gt0; ring_lia.
have -> : a (i + 2) = - (annotated_recs_c.P_cf1 i * a (i + 1) +
                          annotated_recs_c.P_cf0 i * a i)
                          / annotated_recs_c.P_cf2 i.
  apply: canRL (mulfK _) _; rewrite // [LHS]mulrC.
  apply/eqP; rewrite -subr_eq0 opprK addrA; apply/eqP.
  have := a_Sn2 le2i; rewrite /annotated_recs_c.P_horner.
  by rewrite /punk.horner_seqop /= !int.shift2Z -[_ + 1 + 1]addrA.
rewrite /annotated_recs_c.P_cf2 /annotated_recs_c.P_cf1 /annotated_recs_c.P_cf0.
rewrite /alpha /beta.
by field; ring_lia.
Qed.

Local Notation QtoR := (realalg_of _).

(* FIXME : part of this proof would benefit from general lemmas on the *)
(* roots and sign of polynomials of degree 2. To be generalized. *)
Lemma rho_incr (i j : int) : 2%:~R <= i -> 0 <= j -> i <= j -> rho i <= rho j.
Proof.
move=> le0i le0j leij.
suff hsucc (k : int) : 2%:~R <= k -> rho k <= rho (k + 1).
  case: i j le0i leij le0j => [] // i [] // j le2i + _.
  rewrite lez_nat; elim: j => [ |j ihj]; first lia.
  rewrite leq_eqVlt => /predU1P [-> // | leij].
  by rewrite -addn1 PoszD; apply/le_trans/hsucc; [exact: ihj | lia].
move=> le2k {i j le0i le0j leij}.
pose Ralpha i : realalg := QtoR (alpha i).
pose Rbeta i : realalg := QtoR (beta i).
have lt_0_Rbeta (i : int) : 0 <= i -> 0 < Rbeta i%:Q.
  by move=> *; rewrite RealAlg.ltr_to_alg lt_0_beta ?ler0z.
have lt_Rbeta_1 (i : int) : 0 <= i -> Rbeta i%:Q < 1.
  by move=> *; rewrite RealAlg.ltr_to_alg lt_beta_1 ?ler0z.
have lt_Ralpha_0 (i : int) : 0 <= i -> 0 < Ralpha i%:Q.
  by move=> *; rewrite RealAlg.ltr_to_alg lt_0_alpha ?ler0z.
pose hr (i : int) (x : realalg) : realalg := Ralpha i%:Q - Rbeta i%:Q / x.
have h2hr (j : int) (x : rat) : QtoR (h j%:Q x) = hr j (QtoR x).
  rewrite /hr rmorphB /= [QtoR _]lock; congr (_ - _).
  - by rewrite -lock.
  - by rewrite rmorphM /= [QtoR x^-1]fmorphV.
pose p (i : int) (x : realalg) := - (x * x) + Ralpha i%:Q * x - Rbeta i%:Q.
have hr_p (i : int) (x : realalg) : x != 0 -> hr i x - x = (p i x) / x.
  by move=> xneq0; rewrite !mulrDl !mulNr !mulfK // addrC addrA.
have lt0k : 0 < k by apply: lt_le_trans le2k.
have le0k : 0 <= k by apply: ltW.
suff toR : 0 <= p k (QtoR (rho k)).
  rewrite -RealAlg.ler_to_alg -subr_ge0.
  rewrite rho_rec // h2hr hr_p; last first.
    by apply: lt0r_neq0; rewrite RealAlg.ltr_to_alg lt_0_rho.
  by apply: divr_ge0; rewrite ?toR // RealAlg.ler_to_alg ltW // lt_0_rho.
pose deltap (i : int) := QtoR (delta i%:Q).
have deltap_pos (i : int) : 0 <= i -> 0 < deltap i.
  by move=> ?; rewrite /deltap RealAlg.ltr_to_alg lt_0_delta ?ler0z.
pose xp (i : int) : realalg :=
  (Ralpha i%:Q + Num.sqrt (deltap i)) / QtoR (rat_of_Z 2).
pose yp (i : int) : realalg :=
  (Ralpha i%:Q - Num.sqrt (deltap i)) / QtoR (rat_of_Z 2).
have xyp i : 0 <= i -> xp i * yp i = Rbeta i%:Q.
  move=> ?; rewrite mulrC mulrACA -subr_sqr sqr_sqrtr.
    by rewrite /Ralpha /Rbeta /deltap /delta; field.
  exact/ltW/deltap_pos.
have fac_p i x : 0 <= i -> p i x = - ((x - xp i) * (x - yp i)).
  move=> le0i.
  rewrite mulrBl !mulrBr [x * yp i]mulrC !opprB addrAC addrA -mulrDl.
  by rewrite [_ * x - x * x]addrC /p xyp // /xp /yp; field.
have hr_p_pos i t (le0i : 0 <= i) : yp i <= t -> t <= xp i -> 0 <= p i t.
  move=> leypt letxp.
  by rewrite fac_p // oppr_ge0; apply: mulr_le0_ge0; rewrite subr_cp0.
suff rho_in_Iyx i (le2i : 2%:~R <= i) : yp i <= QtoR (rho i) <= xp i.
  by have /andP[yr rx] := rho_in_Iyx _ le2k; apply: hr_p_pos.
have lt_0_xp j : 0 <= j -> 0 < xp j.
  move=> le0j; rewrite /xp; apply: divr_gt0.
    exact/ltr_wpDr/lt_Ralpha_0/le0j/sqrtr_ge0.
  by rewrite RealAlg.ltr_to_alg.
have le_1_xp j (le0j : 0 <= j) : 1 <= xp j.
  rewrite /xp lter_pdivlMr ?mul1r; last by rewrite RealAlg.ltr_to_alg.
  have trans : QtoR (rat_of_Z 2) <= Ralpha j%:Q.
    by apply: ltW; rewrite RealAlg.ltr_to_alg lt_2_alphaN // ler0z.
  apply: le_trans trans _; rewrite lerDl; exact: sqrtr_ge0.
have le_yp_1 j : 2%:~R <= j -> yp j <= 1.
  move=> le2j.
  have le0j : 0 <= j by apply: le_trans le2j; rewrite le0z_nat.
  have -> : yp j = Rbeta j%:Q / xp j.
    by rewrite -xyp // mulrAC mulfV ?mul1r //; apply/lt0r_neq0/lt_0_xp.
  rewrite ler_pdivrMr ?lt_0_xp // mul1r.
  by apply/le_trans/le_1_xp/le0j/ltW/lt_Rbeta_1.
have hr_incr j x y : 0 <= j -> 0 < x -> x <= y -> hr j x <= hr j y.
  move=> le0j lt0x lexy; rewrite -subr_ge0 /hr addrAC [- (Ralpha _ - _)]opprD.
  rewrite opprK addrA addrN add0r -mulrBr; apply: mulr_ge0.
    by rewrite RealAlg.ler_to_alg; apply/ltW/lt_0_beta; rewrite ler0z.
  by rewrite subr_ge0 lef_pV2 // posrE //; apply: lt_le_trans lexy.
suff rho_in_I1x : 1 <= QtoR (rho i) <= xp i.
  by case/andP: rho_in_I1x => h1 ->; rewrite andbT; exact/le_trans/h1/le_yp_1.
suff lerx : QtoR (rho i) <= xp i.
  by rewrite [X in X && _]RealAlg.ler_to_alg le_1_rho //=; apply: le_trans le2i.
suff im_hr j x : 0 <= j -> 0 < x -> x <= xp j -> hr j x <= xp (j + 1).
  have base_case : QtoR (rho 2) <= xp 2.
    rewrite /xp ler_pdivlMr; last by rewrite RealAlg.ltr_to_alg.
    rewrite -lerBlDl; set lhs := (X in X <= _).
    have [le_lhs_0 | lt_0_lhs] := ler0P lhs.
      exact/le_trans/sqrtr_ge0/le_lhs_0.
    rewrite -[lhs]gtr0_norm // -sqrtr_sqr; apply: ler_wsqrtr; rewrite /lhs.
    rewrite -rmorphM /Ralpha -rmorphB -rmorphXn /deltap RealAlg.ler_to_alg.
    have ->: 2%:~R = rat_of_Z 2 by rewrite rat_of_ZEdef.
    by rewrite /delta rho2_eq /alpha [_ <= _]refines_eq; vm_compute.
  case: i le2i; last by discriminate.
  case; first by discriminate.
  case; first by discriminate.
  elim=> [| n ihn] _; first exact: base_case.
  move/(_ (eqxx _)): ihn => ler3x.
  have -> : n.+3 = Posz n.+2 + 1 :> int by rewrite -addn1 PoszD.
  have -> : QtoR (rho (Posz n.+2 + 1)) = hr n.+2 (QtoR (rho n.+2)).
    by rewrite rho_rec // h2hr; exact: lt_0_rho.
  apply: le_trans (im_hr _ _ _ _ ler3x) _; first by [].
    by rewrite RealAlg.ltr_to_alg lt_0_rho.
  exact: le_refl. (* FIXME: done is too slow here *)
move=> le0j lt0x /(hr_incr j _ _ le0j lt0x) {i le2i}.
have -> : hr j (xp j) = xp j.
  apply/eqP; rewrite -subr_eq0 hr_p; last exact/lt0r_neq0/lt_0_xp.
  suff -> : p j (xp j) = 0 by rewrite mul0r.
  by rewrite fac_p // subrr mul0r oppr0.
move=> h; apply: le_trans h _.
suff xp_incr : xp j <= xp (j + 1) by [].
rewrite /xp ler_pM2r; last by rewrite invr_gt0 RealAlg.ltr_to_alg.
apply: lerD.
  by rewrite RealAlg.ler_to_alg rmorphD /=; apply: alpha_incr; rewrite ler0z.
rewrite ler_sqrt; last by try apply/ltW; apply/deltap_pos/addr_ge0.
by rewrite /deltap RealAlg.ler_to_alg rmorphD; apply: delta_incr; rewrite ler0z.
Qed.

Lemma rho_h_iter (n : nat) : (2 <= n)%N -> rho n = h_iter n.
Proof.
elim: n => //; case => //; case => // [_ | n ihn] _.
  by rewrite rho2_eq; apply/eqP; rewrite /h_iter /= [_ == _]refines_eq.
by rewrite -[in LHS]addn1 PoszD rho_rec // ihn.
Qed.

Lemma lt_33_r51 : rat_of_Z 33 < rho (Posz 51).
Proof. by rewrite rho_h_iter // [_ < _]refines_eq; vm_compute. Qed.


(* Here I still do not know which cast we should keep so that's the *)
(* temporary patch to make the pieces fit together. *)
Fact compat33 : rat_of_Z 33 = 33%:Q.
Proof. by rewrite rat_of_ZEdef. Qed.


Notation N_rho := 51%N.

Lemma rho_maj (n : nat) : (N_rho < n)%N -> 33%:Q < rho n.
Proof.
move=> lt_Nrho_n; rewrite -compat33; apply: lt_le_trans lt_33_r51 _.
by apply: rho_incr => //; rewrite lez_nat; apply: leq_trans lt_Nrho_n.
Qed.

Definition Ka :=
  a 1 * ((\prod_(1 <= i < Posz N_rho + 1 :> int) rho i) / 33%:Q ^+ N_rho.+1).

Lemma lt_0_Ka : 0 < Ka.
Proof.
rewrite /Ka; apply: mulr_gt0; first exact: lt_0_a.
apply: divr_gt0; last by rewrite exprn_gt0.
rewrite big_int_cond; apply: prodr_gt0 => i; rewrite andbT => /andP [hi _].
exact/lt_0_rho/le_trans/hi.
Qed.


(* FIXME : lack of _const lemma in bigopz *)
Lemma a_maj (i : int) : 1 < i -> Posz N_rho + 1 < i -> Ka * 33%:Q ^ i < a i.
Proof.
move=> lt1i ltiNrho.
rewrite /Ka; set Ka' := (X in a 1 * X *  _ <_).
suff : Ka' * 33%:Q ^ i < a i / a 1.
  rewrite  [in X in X -> _]ltr_pdivlMr; last exact: lt_0_a.
  by rewrite mulrC [in X in X -> _]mulrA.
rewrite -[X in _ < X](@telescope_prod_int _ 1 i (fun i => a i)) //; last first.
  by move=> /= k /andP [le1k ltki]; apply/a_neq0/le_trans/le1k.
rewrite (big_cat_int _ _ _ _ (ltW ltiNrho)) /=; last by rewrite lerDr.
suff hrho_maj : 33%:Q ^ i / 33%:Q ^+ N_rho.+1 <
                  \prod_(Posz N_rho + 1 <= i0 < i :> int) (a (i0 + 1) / a i0).
  rewrite /Ka' mulrAC -mulrA ltr_pM2l; first exact: hrho_maj.
  rewrite big_int_cond; apply: prodr_gt0 => j; rewrite andbT => /andP [hj _].
  exact/lt_0_rho/le_trans/hj.
rewrite -PoszD; case: i lt1i ltiNrho => i //.
rewrite !ltz_nat addn1 => lt1i ltiNrho.
rewrite eq_big_int_nat /= -expfB // -prodr_const_nat.
by apply: ltr_prod_nat=> [// | j /andP[h51j hji]]; rewrite rho_maj 1?h51j.
Qed.

Lemma a_asympt (n : nat) : (N_rho + 1 < n)%N -> 1 / a n < Ka^-1 / 33%:Q ^ n.
Proof.
move=> hn; rewrite ltr_pdivrMr; last exact: lt_0_a.
rewrite -invfM ltr_pdivlMl; last exact/mulr_gt0/exprz_gt0/isT/lt_0_Ka.
by rewrite mulr1; apply/a_maj/hn/leq_trans/hn.
Qed.
