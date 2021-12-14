Require Import BinInt.

From mathcomp Require Import all_ssreflect all_algebra.
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
Fact Qint_a (i : int)  : a i \is a Qint.
Proof. by apply: rpred_sum => ?; rewrite rpred_zify. Qed.

(* The values of a are strictly positive at positive indexes. *)
Fact lt_0_a (k : int) : 0 <= k -> 0 < a k.
Proof.
move=> h0k; rewrite /a big_int_recl /=; last lia.
apply: ltr_paddr; last exact: lt_0_c.
rewrite big_int_cond; apply: sumr_ge0 => i; rewrite andbT => /andP [] *.
by apply/ltW/lt_0_c; lia.
Qed.

(* The values of a are nonnegative *)
Fact le_0_a (k : int) : 0 <= a k.
Proof.
have [le0k | ltk0] := lerP 0 k; first exact/ltW/lt_0_a.
by rewrite /a big_geqz //; lia.
Qed.

Fact a_neq0 (k : int) : 0 <= k -> a k != 0.
Proof. by move/lt_0_a; rewrite lt0r; case/andP. Qed.

(* a is increasing *)
Fact a_incr (n m : int) : n <= m -> a n <= a m.
Proof.
move=> lenm.
have [le0n | ltn0] := lerP 0 n; last by rewrite {1}/a big_geqz ?le_0_a; lia.
have leSnSm : n + 1 <= m + 1 by lia.
rewrite /a (big_cat_int _ _ _ _ leSnSm) //=; apply: ler_paddr=> //; last first.
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


(* (* TODO : FIX/MOVE *) *)
(* Definition rat_of_positive (p : positive) : rat := rat_of_Z (Z.pos p)%Z. *)

(* Fact lt_0_rat_of_positive (p : positive) : 0 < rat_of_positive p. *)
(* Proof. by rewrite /rat_of_positive rat_of_Z_Zpos. Qed. *)

Fact ltr_rat_of_positive (p1 p2 : positive) :
  (p1 < p2)%positive -> rat_of_positive p1 < rat_of_positive p2.
Proof.
move=> P12; rewrite !rat_of_positiveE ltr_int; exact/ssrnat.ltP/Pos2Nat.inj_lt.
Qed.

Fact ler_rat_of_positive (p1 p2 : positive) :
  (p1 <= p2)%positive -> rat_of_positive p1 <= rat_of_positive p2.
Proof.
move=> P12; rewrite !rat_of_positiveE ler_int; exact/ssrnat.leP/Pos2Nat.inj_le.
Qed.

(* END TODO : FIX/MOVE *)

(* a3_eq and a2_eq should use rat_of_positive *)
Lemma rho2_eq : rho 2 = rat_of_positive 1445 / rat_of_positive 73.
Proof. by rewrite /rho a3_eq a2_eq -!rat_of_Z_rat_of_positive. Qed.

Fact le_1_rho (i : int) : 0 <= i -> 1 <= rho i.
Proof.
move=> lei0; rewrite /rho ler_pdivl_mulr; last exact: lt_0_a.
by rewrite mul1r; apply: a_incr; rewrite ler_paddr.
Qed.

Fact lt_0_rho (i : int) : 0 <= i -> 0 < rho i.
Proof. by move=> lei0; apply/divr_gt0/lt_0_a/lei0/lt_0_a/addr_ge0. Qed.

(* The monotonicity of rho is a consequence of a being solution of Apéry's *)
(* recurrence. We introducte short names for its (fraction) coefficients   *)

(* Let alpha (i : int) := annotated_recs_c.P_cf1 i / annotated_recs_c.P_cf2 i. *)
(* Let beta (i : int) := annotated_recs_c.P_cf0 i / annotated_recs_c.P_cf2 i. *)


(* TODO : FIX/MOVE *)



Definition beta (x : rat) : rat :=
   ((x + rat_of_positive 1) / (x + rat_of_positive 2)) ^+ 3.

(* END TODO *)

Fact lt_0_beta (x : rat) : 0 <= x -> 0 < beta x.
Proof.
by move=> le0i; apply/exprn_gt0/divr_gt0; apply/ltr_paddl/lt_0_rat_of_positive.
Qed.

Fact lt_beta_1 (x : rat) : 0 <= x -> beta x < 1.
Proof.
move=> le0i; rewrite /beta.
have dpos : 0 < x + rat_of_positive 1.
  apply: ltr_paddl; rewrite ?ler0z //; exact: lt_0_rat_of_positive.
have npos : 0 < x + rat_of_positive 2.
  apply: ltr_paddl; rewrite ?ler0z //; exact: lt_0_rat_of_positive.
rewrite expr_lte1 //; last by apply: divr_ge0; apply: ltW.
rewrite ltr_pdivr_mulr // mul1r ltr_add2l; exact: ltr_rat_of_positive.
Qed.

(* TODO : FIX/MOVE *)

Definition alpha (x : rat) :=
  (rat_of_positive 17 * x ^+ 2 + rat_of_positive 51 * x + rat_of_positive 39) *
  (rat_of_positive 2 * x + rat_of_positive 3) / (x + rat_of_positive 2) ^+ 3.


Fact lt_2_alphaN (x : rat) : 0 <= x ->  rat_of_positive 2 < alpha x.
Proof.
move=> le0i; rewrite /alpha.
have npos : 0 < x + rat_of_positive 2.
  apply: ltr_paddl; rewrite ?ler0z //; exact: lt_0_rat_of_positive.
rewrite ltr_pdivl_mulr; last by apply: exprn_gt0.
have trans: rat_of_positive 2 * (x + rat_of_positive 2) ^+ 3 <= 
            rat_of_positive 2 * (x + rat_of_positive 2) ^+ 2 * 
            (rat_of_positive 2 * x + rat_of_positive 3).
  rewrite [_ ^+ 3]exprSr mulrA ler_pmul2l; last first.
    by rewrite pmulr_rgt0 ?exprn_gt0 // lt_0_rat_of_positive.
  apply: ler_add (ler_pemull _ _) (ler_rat_of_positive _) => //.
  suff -> : 1 = rat_of_positive 1 by apply: ler_rat_of_positive.
  by rewrite rat_of_positiveE.
apply: le_lt_trans trans _.
suff trans :  rat_of_positive 2 * (x + rat_of_positive 2) ^+ 2 < 
              rat_of_positive 17 * x ^ 2 + rat_of_positive 51 * x +
              rat_of_positive 39.
  rewrite ltr_pmul2r //; apply/ltr_paddl/lt_0_rat_of_positive.
  rewrite pmulr_rge0 //; exact: lt_0_rat_of_positive.
rewrite -exprnP sqrrD !mulrDr; apply: ler_lt_add; last first. 
  by rewrite [_ < _]refines_eq.
apply: ler_add; first by rewrite ler_wpmul2r ?exprn_ge0 // [_ <= _]refines_eq.
by rewrite [x * _]mulrC mulrA -mulrDl ler_wpmul2r // [_ <= _]refines_eq.
Qed.


Fact lt_0_alpha (x : rat) : 0 <= x -> 0 < alpha x.
Proof.
by move=> le0i; apply/lt_trans/lt_2_alphaN/le0i/lt_0_rat_of_positive.
Qed.

(* A Maple aided proof that - alpha is increasing. *)
Fact alpha_incr (x : rat) : 0 <= x -> alpha x <= alpha (x + 1).
Proof.
move=> le0i; rewrite -subr_ge0; set rhs := (X in 0 <= X).
have hx3 : 0 < x + rat_of_positive 3.
  apply: ltr_paddl; rewrite ?ler0z //; exact: lt_0_rat_of_positive.
have hx2 : 0 < x + rat_of_positive 2.
  apply: ltr_paddl; rewrite ?ler0z //; exact: lt_0_rat_of_positive.
have -> : rhs = (rat_of_positive 51 * x ^+ 4 + 
                 rat_of_positive 456 * x ^+ 3 + 
                 rat_of_positive 1497 * x ^+ 2 + 
                 rat_of_positive 2136 * x + rat_of_positive 1121) / 
                  ((x + rat_of_positive 3) ^+ 3 * (x + rat_of_positive 2) ^+ 3).
  rewrite /rhs /alpha !exprnP. 
  rewrite -!rat_of_Z_rat_of_positive in hx2 hx3 *.
  rewrite rat_of_ZEdef in hx2 hx3.
  by field; rewrite !lt0r_neq0.
apply: divr_ge0; last by apply: mulr_ge0; exact/exprn_ge0/ltW.
apply: addr_ge0; last by rewrite [_ <= _]refines_eq.
have hposM (r : rat) (p : positive) : 0 <= r -> 0 <= rat_of_positive p * r.
  by move=> le0x; exact/mulr_ge0/le0x/ltW/lt_0_rat_of_positive.
apply/addr_ge0/hposM/le0i; do 2! (apply: addr_ge0; last exact/hposM/exprn_ge0).
exact/hposM/exprn_ge0.
Qed.

(* delta is the discriminant *)
Local Definition delta (x : rat) := alpha x ^+ 2 - rat_of_positive 4 * beta x.

Fact lt_0_delta (x : rat) : 0 <= x -> 0 < delta x.
Proof.
move=> le0x; rewrite /delta.
suff trans: 0 <= alpha x ^+ 2 - rat_of_positive 4.
  apply: le_lt_trans trans _; rewrite ltr_add2l -mulNr -[X in X < _]mulr1.
  by rewrite ltr_nmul2l ?lt_beta_1 // [_ <_ ]refines_eq.
have -> : rat_of_positive 4 = (rat_of_positive 2) ^+ 2.
  by apply/eqP; rewrite [_ == _]refines_eq.
rewrite subr_sqr; apply/ltW/mulr_gt0.
  rewrite subr_gt0; exact: lt_2_alphaN.
apply: addr_gt0; rewrite ?lt_0_alpha ?lt_0_rat_of_positive //.
Qed.

(* Maple aided proof again that delta is increasing *)
Lemma delta_incr (x : rat) : 0 <= x -> delta x <= delta (x + 1).
Proof.
move=> le0x; rewrite -subr_ge0; set rhs := (X in 0 <= X).
have hi3 : 0 < x + rat_of_Z 3 by apply/ltr_paddl/rat_of_Z_Zpos.
have hi2 : 0 < x + rat_of_Z 2 by apply/ltr_paddl/rat_of_Z_Zpos.
have -> (n := x) : rhs = (
                 rat_of_Z 3456 * n ^ 10 +
                 rat_of_Z 77550 * n ^  9 +
                 rat_of_Z 777825 * n ^ 8 + 
                 rat_of_Z 4591644 * n ^ 7 + 
                 rat_of_Z 17666100 * n ^ 6 + 
                 rat_of_Z 46291464 * n ^ 5 + 
                 rat_of_Z 83678475 * n ^ 4 + 
                 rat_of_Z 103061566 * n ^ 3 +
                 rat_of_Z 82798770 * n ^ 2 +
                 rat_of_Z 39197496 * n +   
                 rat_of_Z 8307151) / 
                                   ((n + rat_of_Z 3) ^ 6 * (n + rat_of_Z 2) ^ 6).
  rewrite {}/rhs {}/n /delta.
  rewrite /alpha /beta -!rat_of_Z_rat_of_positive !exprnP.
  rewrite rat_of_ZEdef in hi2 hi3.
  by field; rewrite !lt0r_neq0.
by rewrite divr_ge0 ?addr_ge0 ?mulr_ge0 ?addr_ge0.
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
  rewrite /annotated_recs_c.P_cf2; apply: lt0r_neq0. rewrite exprn_gt0 //.
  apply: addr_gt0; last by rewrite rat_of_ZEdef.
  by rewrite -[0]/(0%:Q) ltr_int; apply: lt_le_trans le2i.
have -> : a (i + 2) = - (annotated_recs_c.P_cf1 i * a (i + 1) +
                          annotated_recs_c.P_cf0 i * a i)
                          / annotated_recs_c.P_cf2 i.
  apply: canRL (mulfK _) _; rewrite // [LHS]mulrC.
  apply/eqP; rewrite -subr_eq0 opprK addrA; apply/eqP.
  have := a_Sn2 le2i; rewrite /annotated_recs_c.P_horner.
  by rewrite /punk.horner_seqop /= !int.shift2Z -[_ + 1 + 1]addrA.
rewrite /annotated_recs_c.P_cf2 /annotated_recs_c.P_cf1 /annotated_recs_c.P_cf0.
by rewrite /alpha /beta -!rat_of_Z_rat_of_positive !exprnP; field; ring_lia.
Qed.

Local Notation QtoR := (realalg_of _).

(* FIXME : part of this proof would benefit from general lemmas on the *)
(* roots and sign of polynomials of degree 2. To be generalized. *)
Lemma rho_incr (i j : int) : 2%:~R <= i -> 0 <= j -> i <= j -> rho i <= rho j.
Proof.
move=> le0i le0j leij.
suff hsucc (k : int) : 2%:~R <= k -> rho k <= rho (k + 1).
  case: i le0i leij => // i le2i; case: j le0j => // j _.
  elim: j => [ |j ihj]; first by rewrite lez_nat leqn0; move/eqP->.
  rewrite lez_nat leq_eqVlt => /predU1P [-> // | leij].
  rewrite -addn1 PoszD; apply/le_trans/hsucc; first exact: ihj.
  by apply: le_trans le2i _; rewrite lez_nat.
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
have deltapE (i : int) : 
  deltap i = (Ralpha i%:Q) ^+ 2 - QtoR (rat_of_positive 4) * (Rbeta i%:Q).
  rewrite /deltap /delta rmorphD rmorphN rmorphX /=.
  by rewrite [QtoR (_ * beta i%:Q)]rmorphM.
have deltap_pos (i : int) : 0 <= i -> 0 < deltap i.
  move=> ?; rewrite /deltap RealAlg.ltr_to_alg; apply: lt_0_delta.
  by rewrite ler0z.
pose xp (i : int) : realalg := 
  ((Ralpha i%:Q) + Num.sqrt (deltap i)) / QtoR (rat_of_positive 2).
pose yp (i : int) : realalg := 
  ((Ralpha i%:Q) - Num.sqrt (deltap i)) / QtoR (rat_of_positive 2).
have {deltapE} xyp i : 0 <= i -> (xp i) * (yp i) = Rbeta i%:Q.
  move=> ?; rewrite mulrC /xp /yp mulrAC !mulrA -subr_sqr.
  rewrite sqr_sqrtr; last exact/ltW/deltap_pos.
  rewrite deltapE opprD opprK addrA addrN add0r -mulrA mulrC mulrA -invfM.
  rewrite -rmorphM /=.
  have -> : rat_of_positive 2 * rat_of_positive 2 = rat_of_positive 4.
    by apply/eqP; rewrite [_ == _]refines_eq.
  rewrite mulVf ?mul1r //; apply: lt0r_neq0; rewrite RealAlg.ltr_to_alg.
  exact: lt_0_rat_of_positive.
have x_plus_yp i : (xp i) + (yp i) = Ralpha i%:Q.
  rewrite /xp /yp -mulrDl addrAC addrA addrNK -{-3}[Ralpha i%:Q]mulr1.
  rewrite -mulrDr -mulrA.
  suff -> : ((1 + 1) / QtoR (rat_of_positive 2)) = 1 by rewrite mulr1.
    rewrite -[1]/(QtoR 1) -rmorphD -fmorphV -rmorphM /=; congr QtoR.
    have -> : 1 + 1 = rat_of_positive 2 by apply/eqP; rewrite [_ == _]refines_eq. 
    by apply/eqP; rewrite [_ == _]refines_eq. 
have {x_plus_yp} fac_p i x (le0i : 0 <= i) :
     p i x  = - ((x - (xp i)) * (x - (yp i))).
  rewrite mulrBl !mulrBr [x * yp i]mulrC !opprB addrAC addrA -mulrDl.
  by rewrite [_ * x - x * x]addrC /p xyp // x_plus_yp.
have hr_p_pos i t (le0i : 0 <= i) : yp i <= t -> t <= xp i -> 0 <= p i t.
  move=> leypt letxp.
  by rewrite fac_p // oppr_ge0; apply: mulr_le0_ge0; rewrite subr_cp0.
suff rho_in_Iyx i (le2i : 2%:~R <= i) : yp i <= QtoR (rho i) <= xp i.
  by have /andP[yr rx] := rho_in_Iyx _ le2k; apply: hr_p_pos.
have lt_0_xp j : 0 <= j -> 0 < xp j.
  move=> le0j; rewrite /xp; apply: divr_gt0.
    exact/ltr_paddr/lt_Ralpha_0/le0j/sqrtr_ge0.
  rewrite RealAlg.ltr_to_alg; exact: lt_0_rat_of_positive.
have le_1_xp j (le0j : 0 <= j) : 1 <= xp j.
  rewrite /xp lter_pdivl_mulr ?mul1r; last first.
    rewrite RealAlg.ltr_to_alg; exact: lt_0_rat_of_positive.
  have trans : QtoR (rat_of_positive 2) <= Ralpha j%:Q.
    by apply: ltW; rewrite RealAlg.ltr_to_alg lt_2_alphaN // ler0z.
  apply: le_trans trans _; rewrite ler_addl; exact: sqrtr_ge0.
have le_yp_1 j : 2%:~R <= j -> yp j <= 1.
  move=> le2j.
  have le0j : 0 <= j by apply: le_trans le2j; rewrite le0z_nat.
  have -> : yp j = Rbeta j%:Q / xp j.
    by rewrite -xyp // mulrAC mulfV ?mul1r //; apply/lt0r_neq0/lt_0_xp.
  rewrite ler_pdivr_mulr ?lt_0_xp // mul1r.
  by apply/le_trans/le_1_xp/le0j/ltW/lt_Rbeta_1.
have hr_incr j x y : 0 <= j -> 0 < x -> x <= y -> hr j x <= hr j y.
  move=> le0j lt0x lexy; rewrite -subr_ge0 /hr addrAC [- (Ralpha _ - _)]opprD.
  rewrite opprK addrA addrN add0r -mulrBr; apply: mulr_ge0.
    by rewrite RealAlg.ler_to_alg; apply/ltW/lt_0_beta; rewrite ler0z.
  by rewrite subr_ge0 lef_pinv // posrE //; apply: lt_le_trans lexy.
suff rho_in_I1x : 1 <= QtoR (rho i) <= xp i.
  by case/andP: rho_in_I1x => h1 ->; rewrite andbT; exact/le_trans/h1/le_yp_1.
suff lerx : QtoR (rho i) <= xp i.
  by rewrite [X in X && _]RealAlg.ler_to_alg le_1_rho //=; apply: le_trans le2i.
suff im_hr j x : 0 <= j -> 0 < x -> x <= xp j -> hr j x <= xp (j + 1).
  have base_case : QtoR (rho 2) <= xp 2.
    have squared (prat2 := rat_of_positive 2) :
        (rho 2 * prat2 - alpha prat2) ^+ 2 <= delta prat2.
      by rewrite /delta rho2_eq /alpha /prat2 [_ <= _]refines_eq; vm_compute.
    rewrite /xp ler_pdivl_mulr; last first.
    - by rewrite RealAlg.ltr_to_alg lt_0_rat_of_positive.
    rewrite -ler_subl_addl; set lhs := (X in X <= _).
    have [le_lhs_0 | lt_0_lhs] := ler0P lhs.
      exact/le_trans/sqrtr_ge0/le_lhs_0.
    rewrite -[lhs]gtr0_norm // -sqrtr_sqr; apply: ler_wsqrtr; rewrite /lhs.
    rewrite -rmorphM /Ralpha -rmorphB -rmorphX /deltap RealAlg.ler_to_alg.
    by rewrite -[2%N]/(Pos.to_nat 2) -rat_of_positiveE.
  case: i le2i; last by discriminate.
  case; first by discriminate.
  case; first by discriminate.
  elim=> [| n ihn] _; first exact: base_case.
  move/(_ (eqxx _)): ihn => ler3x.
  have -> : n.+3 = Posz n.+2 + 1 :> int by rewrite -addn1 PoszD.
  have -> : QtoR (rho (Posz n.+2 + 1)) = hr n.+2 (QtoR (rho n.+2)).
    rewrite rho_rec // h2hr // ; exact: lt_0_rho.
  apply: le_trans (im_hr _ _ _ _ ler3x) _ => //.
  rewrite RealAlg.ltr_to_alg; exact: lt_0_rho.
move=> le0j lt0x /(hr_incr j _ _ le0j lt0x) {i le2i}.
have -> : hr j (xp j) = xp j.
  apply/eqP; rewrite -subr_eq0 hr_p; last exact/lt0r_neq0/lt_0_xp.
  suff -> : p j (xp j) = 0 by rewrite mul0r.
  by rewrite fac_p // subrr mul0r oppr0.
move=> h; apply: le_trans h _.
suff xp_incr : xp j <= xp (j + 1) by [].
rewrite /xp ler_pmul2r; last first.
  by rewrite invr_gt0 RealAlg.ltr_to_alg lt_0_rat_of_positive.
apply: ler_add.
  by rewrite RealAlg.ler_to_alg rmorphD /=; apply: alpha_incr; rewrite ler0z.
rewrite ler_sqrt; last exact/deltap_pos/addr_ge0.
by rewrite /deltap RealAlg.ler_to_alg rmorphD; apply: delta_incr; rewrite ler0z.
Qed.

Lemma rho_h_iter (n : nat) : (2 <= n)%N -> rho n = h_iter n.
Proof.
elim: n => //; case => //; case => // [_ | n ihn] _.
  by rewrite rho2_eq; apply/eqP; rewrite /h_iter /= [_ == _]refines_eq.
by rewrite -[in LHS]addn1 PoszD rho_rec // ihn.
Qed.

Lemma lt_33_r51 : rat_of_positive 33 < rho (Posz 51).
Proof. by rewrite rho_h_iter // [_ < _]refines_eq; vm_compute. Qed.


(* Here I still do not know which cast we should keep so that's the *)
(* temporary patch to make the pieces fit together. *)
Fact compat33 : rat_of_positive 33 = 33%:Q.
Proof. by rewrite -rat_of_Z_rat_of_positive rat_of_ZEdef. Qed.


Notation N_rho := 51.

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
  rewrite  [in X in X -> _]ltr_pdivl_mulr; last exact: lt_0_a.
  by rewrite mulrC [in X in X -> _]mulrA.
rewrite -[X in _ < X](@telescope_prod_int _ 1 i (fun i => a i)) //; last first.
  by move=> /= k /andP [le1k ltki]; apply/a_neq0/le_trans/le1k.
rewrite (big_cat_int _ _ _ _ (ltW ltiNrho)) /=; last by rewrite ler_addr.
suff hrho_maj : 33%:Q ^ i / 33%:Q ^+ N_rho.+1 < 
                  \prod_(Posz N_rho + 1 <= i0 < i :> int) (a (i0 + 1) / a i0).
  rewrite /Ka' mulrAC -mulrA ltr_pmul2l; first exact: hrho_maj.
  rewrite big_int_cond; apply: prodr_gt0 => j; rewrite andbT => /andP [hj _].
  exact/lt_0_rho/le_trans/hj.
rewrite -PoszD; case: i lt1i ltiNrho => i //.
rewrite !ltz_nat addn1 => lt1i ltiNrho.
rewrite eq_big_int_nat /= -expfB // -prodr_const_nat.
by apply: ltr_prod_nat=> [// | j /andP[h51j hji]]; rewrite rho_maj 1?h51j. 
Qed.

Lemma a_asympt (n : nat) : (N_rho + 1 < n)%N -> 1 / a n < Ka^-1 / 33%:Q ^ n.
Proof.
move=> hn; rewrite ltr_pdivr_mulr; last exact: lt_0_a.
rewrite -invfM ltr_pdivl_mull; last exact/mulr_gt0/exprz_gt0/isT/lt_0_Ka.
by rewrite mulr1; apply/a_maj/hn/leq_trans/hn.
Qed.
