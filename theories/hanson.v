Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_field.

Require Import arithmetics multinomial floor posnum binomialz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import field_tactics.
Require Import bigopz.
Require Import lia_tactics conj.
Require Import shift.
Require Import extra_mathcomp.

Require Import hanson_elem_arith.
Require Import hanson_elem_analysis.

Import Order.TTheory GRing.Theory Num.Theory.


(******************************************************************************)
(*   An elementary proof that lcm (1 ... n) = O(3^n), following               *)
(* 'On the product of the primes', D. Hanson, Canad. Math. Bull. 1972         *)
(******************************************************************************)


(* The proof works by studying C(n) > lcm(1 ... n), defined by the means of the
   auxiliary sequence a(n), defined as follow: *)

(* Elementary sequence definitions and properties are in hanson_elem_arith.v *)
(* elementary definitions and properties of rational exponents are in
hanson_elem_analysis.v *)

(* Notation "r '%C'" := ((ratr r) : algC) (at level 8). (* random level *) *)

(* Lemma 3 from original paper *)

Section Missing.

Variable R : numFieldType.
(* Implicit Type x1 x2 y1 y2 x y : nat. *)

Lemma ltr_pmul_le_l (x1 y1 x2 y2 : R):
   0 < x1 -> 0 < x2 -> x1 <= y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Proof.
rewrite le_eqVlt => posx1 posx2 /predU1P[<-|lt1] lt2.
  by rewrite ltr_pmul2l.
by apply: ltr_pmul=> //; exact: ltW.
Qed.

Lemma ltr_pmul_le_r (x1 y1 x2 y2 : R):
   0 < x1 -> 0 < x2 -> x1 < y1 -> x2 <= y2 -> x1 * x2 < y1 * y2.
Proof.
move => Hx1 Hx2 Hx1y1 Hx2y2; rewrite mulrC [y1*y2]mulrC; exact: ltr_pmul_le_l.
Qed.

Lemma exp_incr_expp (x : R) (H1x : 1 <= x) (m n : nat) :
  (m <= n)%nat -> x ^+ m <= x ^+ n.
Proof. 
move => Hmn; have Hx : 0 < x by apply: lt_le_trans H1x.
have H : 0 < x ^+ m by rewrite exprn_gt0.
rewrite -(subnKC Hmn) exprD mulrC -ler_pdivr_mulr ?divrr ?unitf_gt0 //. 
by rewrite exprn_ege1.
Qed.

Lemma exp_incr_expn (x : R) (H1x : 0 < x < 1) (m n : nat) :
  (n <= m)%nat -> x ^+ m <= x ^+ n.
Proof.
move => Hmn; rewrite -(subnKC Hmn) exprD mulrC; case/andP: H1x => H0 H1.
by rewrite ger_pmull ?exprn_gt0 //; apply: exprn_ile1 => //; apply: ltW.
Qed.

Lemma exp_quo_0 p q : exp_quo 0 p q = (p == 0%nat)%:R.
Proof. by rewrite /exp_quo /ratr mul0r rootC0 expr0n. Qed.

Lemma C_n0 n : C n 0 = n `!.
Proof. by have := C_multi n 0; rewrite big_nil mul1n. Qed.

Lemma iter_lcmn1 : iter_lcmn 1 = 1%nat.
Proof. by rewrite iter_lcmnS iter_lcmn0 lcmn1. Qed.

End Missing.

Module Hanson.

Import Num.Internals.

Section PreliminaryRemarksLemma7.

Variables (n i : nat).
Hypothesis Hain : (a i <= n)%N.

Lemma remark_7_1 : ((n.+1 - a i) <= (n %/ a i) * (a i))%N .
Proof.
have H1n : (1 < n)%N by apply: leq_trans (a_gt1 i) _.
move: Hain; rewrite leq_eqVlt; case/orP => [|h].
  by move/eqP ->; rewrite subSnn divnn (ltnW H1n) mul1n; exact: leq_trans H1n.
by rewrite leq_subLR {1}(divn_eq n (a i)) addnC ltn_add2r ltn_mod; exact: a_pos.
Qed.

Lemma remark_7_2  :
   exp_quo ((n.+1 - a i)%N%:Q / (a i)%:Q) (n.+1 - a i)%N (a i) <=
   (((n %/ (a i)) ^ (n %/ (a i)))%N%:Q)%:C.
Proof.
rewrite exp_quo_nat_nat; apply: exp_quo_self_grows => // .
- by rewrite divr1.
- rewrite divr_gt0 // ?ltr0n ?(a_pos i) // .
    by rewrite subn_gt0.
  by rewrite extra_mathcomp.ler1z lez_nat divn_gt0 ?a_pos //.
rewrite ler_pdivr_mulr ?ltr0n ?a_pos // -intrM. rewrite ler_int lez_nat.
exact: remark_7_1.
Qed.

Lemma remark_7_3 :
let f := fun u x y => exp_quo (u / (a i)%:Q) x y in
    f n%:Q n (a i) / ((n %/ (a i)) ^ (n %/ (a i)))%N%:Q%:C
  <= f n%:Q n (a i) / f (n.+1 - a i)%N%:Q (n.+1 - a i)%N (a i).
Proof.
have Ha1 : (0 <= a i)%N by exact: (ltnW (a_pos i)).
have Ha2 : (0 < a i)%N by exact: (a_pos i).
rewrite /= ler_pdivr_mulr; last first.
  by rewrite ltr0q ltr0n // expn_gt0 divn_gt0 // Hain.
rewrite[X in _ <= X]mulrC mulrA ler_pdivl_mulr.
- rewrite mulrC; apply: ler_pmul; try rewrite lexx // .
  + by apply: exp_quo_ge0 => //; rewrite divr_ge0 // ?ler0z //.
  + by apply: exp_quo_ge0 => //; rewrite divr_ge0 // ?ler0z //.
  + exact: remark_7_2.
- by apply: exp_quo_gt0 => //; rewrite divr_gt0 // ?ltr0n // subn_gt0.
Qed.

(* This one would ideally be entirely automated *)
Lemma remark_7_4 :
let r := (n.+1 - a i)%N%:Q / (a i - 1)%N%:Q in
  (exp_quo (n%:Q / (a i)%:Q) n%N (a i) /
           exp_quo ((n.+1 - a i)%N%:Q / (a i)%:Q) (n.+1 - a i)%N (a i)) ^+ (a i) =
  (exp_quo (1 + 1 / r) (n.+1 - a i)%N (a i)) ^+(a i) *
  ((n%:Q / (a i)%:Q) ^ (a i - 1)%N)%:C.
Proof.
move => r.
have Hapos := a_pos i.
have npos : (0 < n)%N by exact: (leq_trans Hapos).
have helper1 : (n < a i + n)%N by rewrite -{1}[n]add0n ltn_add2r.
have -> : (1 + 1 / r) = n%:Q / (n.+1 - a i)%N%:Q. (* automation missing...*)
  rewrite /r -addn1 -!subzn // ; last by rewrite addn1 leqW.
  rewrite // ?rmorphD /= ?rmorphN //= !PoszD !rmorphD /= .
  rat_field. rewrite /emb /emb0.
  split.
    suff: (a i)%:Q < (n + 1)%N%:Q by goal_to_lia; intlia.
      by rewrite ltr_nat addn1.
    suff : 1%:Q < (a i)%:Q. by goal_to_lia; intlia.
      by rewrite ltr_nat a_gt1.
suff {1}<- : (n%:Q / (a i)%:Q) * ((n.+1 - a i)%N%:Q / n%:Q) =
             (n.+1 - a i)%N%:Q / (a i)%:Q.
  rewrite -[X in (_ / X)^+ _ = _]exp_quo_mult_distr ?divr_ge0 ?ler0n // .
  rewrite [in LHS]exprMn.
  rewrite exprVn.
  rewrite [in LHS]exprMn.
  rewrite [X in (_ / X)]mulrC invrM ?GRing.unitfE ?extra_mathcomp.lt0r_neq0 // .
  + rewrite mulrA exprnN {1 2}/exp_quo -exprM mulnC exprM rootCK // .
    rewrite [(a i).-root (ratr (n%:~R / (a i)%:~R)) ^+ (n.+1 - a i)]exprnP.
    rewrite exprz_exp.
    rewrite mulrN [(Posz(n.+1 - a i)%N * (a i))]mulrC -mulrN -exprz_exp -exprnP.
    rewrite rootCK // -exprnN.
    rewrite -GRing.exprB ?leq_subLR ?unitf_gt0 //; last first.
       by rewrite ltr0q divr_gt0 // ltr0n.
    rewrite subnBA ?leqW // .
    have -> : (n + a i - n.+1 = a i - 1)%N by rewrite -addn1 subnDl.
    rewrite [RHS]mulrC.
    congr (_ * _).
      by rewrite exprnP rmorphX.
    have -> : exp_quo ((n.+1 - a i)%N%:~R / n%:~R) (n.+1 - a i) (a i) ^- a i =
                ratr ((n.+1 - a i)%N%:~R / n%:~R) ^ (- (n.+1 - a i)%N%:Z).
      by rewrite exprnP -exprnP -exprM exprnP mulnC -exprnP exprM rootCK ?exprnN.
    rewrite -exprz_inv; repeat (rewrite CratrE /=); rewrite invrM /= ?invrK.
    * by rewrite /exp_quo; repeat (rewrite CratrE /=);
        rewrite -exprM mulnC exprM rootCK -?exprnP.
    * by rewrite unitf_gt0 // ltr0n subn_gt0.
    * rewrite unitf_gt0 // invr_gt0 ltr0n.
      exact: (leq_trans Hapos).
  + by rewrite exprn_gt0 // exp_quo_gt0 // divr_gt0 // ltr0n ?subn_gt0.
  + by rewrite exprn_gt0 // exp_quo_gt0 // divr_gt0 // ltr0n.
rat_field.
rewrite /emb /emb0.
split.
suff : 0%:Q < (a i)%:Q by goal_to_lia; intlia.
  by rewrite ltr_nat.
suff : 0%:Q < (n)%:Q by goal_to_lia; intlia.
  by rewrite ltr_nat.
Qed.

End PreliminaryRemarksLemma7.

(* Notation "2" := 2%:R : ring_scope. *)


(* TODO rename + chainage avant *)
Lemma l7 n i (Hain : (a i <= n)%N) :
  exp_quo (n%:Q / (a i)%:Q) n (a i) / ((n %/ (a i)) ^ (n %/ (a i)))%N%:Q%:C <
  exp_quo (10%:Q * n%:Q / (a i)%:Q) (a i - 1) (a i).
Proof.
have Hapos := a_pos i.
have posai_rat : 0 < (a i)%:~R :> rat by rewrite ltr0n.
pose posai := PosNumDef posai_rat.
have -> : (a i)%:~R = num_of_pos posai by [].
have lt0n : (0 < n)%N by exact: (leq_trans Hapos).
have lt0n_rat : 0 < n%:~R :> rat by rewrite ltr0n.
pose posn := PosNumDef lt0n_rat.
have -> :  n%:~R = num_of_pos posn by [].
apply: le_lt_trans (remark_7_3 Hain) _.
set lhs := (X in X < _); set rhs := (X in _ < X).
suff : lhs ^+ (a i) < rhs ^+ (a i).
  have lhs_ge0 : 0 <= lhs.
  (* roots, hence alg. numbers prevent using posnum based automation *)
    by rewrite /lhs divr_ge0 // exp_quo_ge0 // divr_ge0 // ?ler0n // ler0q.
  have rhs_ge0 : 0 <= rhs by rewrite /rhs exp_quo_ge0.
  by rewrite ltr_pexpn2r.
rewrite remark_7_4 // /rhs.
rewrite -mulrA -exp_quo_mult_distr // exprMn. 
have -> : exp_quo 10%:~R (a i - 1) (a i) ^+ a i = exp_quo 10%:~R (a i - 1)%N 1.
  by rewrite /exp_quo -exprM mulnC exprM rootCK // root1C.
have -> :  exp_quo (n%:~R / (a i)%:~R) (a i - 1) (a i) ^+ a i =
           ratr ((n%:~R / (a i)%:~R) ^ (a i - 1)%N).
  by rewrite /exp_quo -exprM mulnC exprM rootCK // rmorphX.  
rewrite -lter_pdivr_mulr //; last first.
  by rewrite ltr0q exprz_gt0 // divr_gt0 // ltr0n.
rewrite -mulrA divrr; last first.
  by rewrite unitf_gt0 // ltr0q exprz_gt0 // divr_gt0 // ltr0n .
rewrite mulr1 -exp_quo_r_nat.
rewrite rmorphX /=.
repeat (rewrite CratrE /=).
set x := (n.+1 - a i)%N.
set y := (a i - 1)%N.
set z := (a i).
have Hx : (0 < x)%N by rewrite subn_gt0.
have Hy : (0 < y)%N by rewrite subn_gt0 a_gt1.
have Hxy : (0 < x * y)%N by rewrite muln_gt0 Hx Hy.
have Hzy : (0 < z * y)%N by rewrite muln_gt0 Hapos Hy.
have -> : exp_quo (1 + 1 / (x%:~R / y%:~R)) x z =
          exp_quo (1 + 1 / (x%:~R / y%:~R)) (x*y)%N (z*y)%N.
  apply: exp_quo_equiv => //; last by rewrite -mulnA [(y*z)%N]mulnC.
  by rewrite -[0]addr0 ler_add // divr_ge0 // divr_ge0 // ?ler0n.
have side1 : 0 <= ratr (1 + 1 / (x%:~R / y%:~R)) :> algC.
  by rewrite ler0q -[0]addr0 ler_add // divr_ge0 // divr_ge0 // ler0n.
rewrite /exp_quo prod_root // exprM -rootCX //; last by rewrite rootC_ge0.
rewrite -exprM mulnC exprM rootCK ?ltr_pexpn2r // ?nnegrE ?ler0n //; last first. 
- by apply: exprn_ge0; rewrite rootC_ge0.
have -> : y.-root (ratr (1 + 1 / (x%:~R / y%:~R))) ^+ x =
          exp_quo (1 + 1 / (x%:R / y%:R)) x y.
  by rewrite /exp_quo //; repeat (rewrite CratrE /=).
apply: le_lt_trans. apply one_plus_invx_expx => //.
- by rewrite divr_gt0 // ltr0n.
- do 2! (rewrite CratrE /=); exact: ltr_nat.
Qed.


(* First inequality on C *)
Lemma l10 n k (Hank : (a k <= n)%N) :
  (C n k.+1)%:Q%:C <
  (n ^ n)%N%:Q%:C *
  \prod_(i < k.+1) (exp_quo (10%:Q * n%:Q / (a i)%:Q) ((a i).-1) (a i)) /
  \prod_(i < k.+1) (exp_quo (n%:Q / (a i)%:Q) n (a i)).
Proof.
have lt0n : (0 < n)%N by exact: (leq_trans (a_pos k)).
suff Hinterm :
  ((n ^ n)%N%:Q / (\prod_(i < k.+1) (n %/ (a i)) ^ (n %/ a i))%N%:Q)%:C
  < (n ^ n)%N%:Q %:C *
   \prod_(i < k.+1) exp_quo (10%:Q * n%:Q / (a i)%:Q) (a i).-1 (a i) /
   \prod_(i < k.+1) exp_quo (n%:Q / (a i)%:Q) n (a i).
  apply: le_lt_trans Hinterm.
  repeat (rewrite CratrE /=); rewrite ler_pdivl_mulr.
    rewrite mulrC -natrM ler_nat.
    by move: (l8 n k.+1); rewrite big_mkord.
  rewrite ltr0n prodn_gt0 // => i; rewrite expn_gt0.
  by case: (posnP (n %/ a i)%N).
rewrite ltr_pdivl_mulr; last first.
  apply: prodr_gt0 => i _.
  by rewrite exp_quo_gt0  ?divr_ge0 ?divr_gt0 ?ltr0n ?a_pos.
rewrite -lter_pdivr_mulr; last first.
  apply: prodr_gt0 => i _.
  by rewrite exp_quo_gt0  ?divr_ge0 1?divr_gt0 1?mulr_gt0 ?ltr0n // ?a_pos.
rewrite CratrE /= -2!mulrA.
rewrite gtr_pmulr; last first.
  by rewrite ltr0q ltr0n expn_gt0 lt0n.
rewrite mulrA lter_pdivr_mulr; last first.
  apply: prodr_gt0 => i _.
  by rewrite exp_quo_gt0  ?divr_ge0 1?divr_gt0 1?mulr_gt0 ?ltr0n // ?a_pos.
rewrite mul1r mulrC.
rewrite CratrE /= CratrE /= CratrE /= .
have -> :
  \prod_(i < k.+1) exp_quo (n%:~R / (a i)%:~R) n (a i) /
   (\prod_(i < k.+1) (n %/ a i) ^ (n %/ a i))%:R =
  \prod_(i < k.+1)
   (exp_quo (n%:~R / (a i)%:~R) n (a i) /
            ((n %/ a i) ^ (n %/ a i))%:R).
  by rewrite natr_prod -prodf_div.
rewrite 2!big_ord_recr /= ltr_pmul_le_l // ?prodr_gt0 1?divr_gt0 //
        1?ltr0n 1?exp_quo_gt0 // 1?divr_gt0 ?ltr0n 1?a_pos // .
+ move => i H. 
  rewrite divr_gt0 ?lertn // ?exp_quo_gt0 ?divr_gt0 1?a_pos1 ?ltr0n ?a_pos //. 
  by rewrite expn_gt0; case: (posnP (n %/ a i)%N).
+ rewrite expn_gt0; by case: (posnP (n %/ a k)%N).
+ apply: ler_prod => i _; apply/andP. 
  split; first by rewrite divr_ge0 ?exp_quo_ge0 ?a_pos ?divr_ge0 ?ler0n.
  (* rewrite ltrW // . *)
  have Hain : (a i <= n)%N.
    suff Hik : (a i <= a k)%N by apply: (leq_trans _ Hank).
    by apply: a_grows; case: i => i /= Hi; exact: ltnW.
  move:  (l7 Hain); rewrite CratrE /= CratrE /= subn1; exact: ltW.
+ by move: (l7 Hank); rewrite CratrE /= CratrE /= subn1.
Qed.

Section A'.

Implicit Types i : nat.

Definition a' i : algC := exp_quo (a i)%:Q 1%N (a i).

Lemma a'_ge0 i : 0 <= a' i.
Proof. by rewrite rootC_ge0 ?CratrE ?ler0n ?a_pos. Qed.
Hint Resolve a'_ge0.

Lemma a'_gt0 i : 0 < a' i.
Proof.
by rewrite rootC_gt0 ?CratrE ?ltr0n ?a_pos.
Qed.
Hint Resolve a'_gt0.

Lemma a'_gt1 i : 1 < a' i.
Proof.
by rewrite exprn_egte1 // rootC_gt1 ?ltr1q ?ltr1n ?a_gt1 ?a_pos.
Qed.
Hint Resolve a'_gt1.

Lemma a'_S i (Hi : (2 <= i)%N) : a' i.+1 <= sqrtC (a' i).
Proof.
rewrite /a' /exp_quo !expr1.
case/andP: (Observation_compare_a_a i) => H1 H2.
repeat (rewrite CratrE /=); rewrite -/(a i.+1).
have Hinterm : (a i.+1).-root (a i.+1)%:R <= (a i.+1).-root (a i ^ 2)%:R :> algC.
  by rewrite ler_rootC ?a_pos // ?nnegrE ?ler0n // ler_nat // ltnW.
apply: (le_trans Hinterm) => {Hinterm}.
have Hinterm1 : (a i.+1).-root (a i ^ 2)%:R <=
                (((a i).-1)^2)%N.-root ((a i) ^2)%N%:R :> algC.
  rewrite rootC_leq // ?ler1n ?sqrn_gt0 -?subn1 ?subn_gt0 ?a_gt1 ?a_pos // .
  by rewrite subn1 ltnW.
rewrite (le_trans Hinterm1) // => {Hinterm1}.
rewrite -prod_root // ?a_pos ?ler0n ?ltnW // .
rewrite -[(a i)%:R](@rootCK _ 2%N) //  -rootCX // ?ler0n // .
rewrite -[in X in (_ <= X)]prod_root //= ?muln_gt0 ?a_pos // ?GRing.natrX;
  last first.
  by rewrite -natrX ?ler0n.
rewrite rootC_leq // ?muln_gt0 ?a_pos -?natrX ?ler1n ?expn_gt0 ?a_pos // .
rewrite -lez_nat !PoszM -subn1 -subzn ?a_pos // .
rewrite -subr_ge0.
set rhs := (X in 0 <= X).
have -> : rhs = (a i)%:Z  * ((a i)%:Z - 6%:Z) + 1.
  rewrite -eqr_int_prop !intrD !intrM !intrD !rmorphN !rmorphM /= .
  by rat_field.
rewrite addr_ge0 // mulr_ge0 // subr_ge0.
have Ha2 : (5 < a 2)%N by []. 
apply: (leq_trans Ha2); exact: a_grows.
Qed.

Lemma a'_bound i j (Hi : (2 <= i)%N) : a' (i+j) <= (2^j%N).-root (a' i).
Proof.
elim: j => [|j HIj] //.
  by rewrite addn0 expn0 root1C.
rewrite addnS.
have /a'_S Ha : (2 <= i + j)%N by apply: (leq_trans Hi); rewrite leq_addr.
apply: (le_trans Ha).
rewrite expnS prod_root // ?expn_gt0 // ?rootC_ge0 ?a_pos ?CratrE ?ler0n // .
rewrite ler_rootC ?nnegrE // .
by rewrite rootC_ge0 ?CratrE ?ler0n ?a_pos // ?expn_gt0.
Qed.

Section W_k.

Definition w_seq k := \prod_(i < k) a' i.

Lemma w_seq_ge0 k : 0 <= w_seq k.
Proof.
by rewrite prodr_ge0 // => i _ ; exact:a'_ge0.
Qed.

Lemma w_seq_gt0 k : 0 < w_seq k.
Proof.
by rewrite prodr_gt0 // => i _ ; exact:a'_gt0.
Qed.

Lemma w_seq_le_S k : w_seq k <= w_seq k.+1.
Proof.
  rewrite /w_seq big_ord_recr /= .
  by rewrite ler_pmulr 1?ltW ?a'_gt1 // prodr_gt0 // => i _ .
Qed.

Lemma w_seq_incr k l : (k <= l)%N -> w_seq k <= w_seq l.
Proof.
elim: l => [|l ihl]; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt ltnS; case/orP => [/eqP-> // | /ihl hkl].
exact: le_trans (w_seq_le_S _).
Qed.


Lemma w_seq_bound k (Hk : (2 <= k)%N) l :
  w_seq (k + l) <= w_seq k * exp_quo ((a k)%:Q) (2 ^ l.+1 - 2)%N (2 ^ l * (a k))%N.
Proof.
elim: l => [|l HIl].
  by rewrite addn0 /= expn1 subnn /= /exp_quo expr0 mulr1.
rewrite addnS /w_seq big_ord_recr /=.
suff -> : exp_quo (a k)%:~R (2 ^ l.+2 - 2) (2 ^ l.+1 * a k) = 
          exp_quo (a k)%:~R (2 ^ l.+1 - 2) (2 ^ l * a k) * (2^l%N).-root (a' k).
  rewrite mulrA.
  apply: ler_pmul; rewrite ?a'_bound // ?rootC_ge0 ?CratrE ?a_pos ?ler0n // .
  by rewrite prodr_ge0 // => i _ ; exact: a'_ge0.
rewrite -prod_root ?CratrE ?expn_gt0 ?a_pos ?ler0n // .
have -> : (2 ^ l * a k).-root (a k)%:R = exp_quo (a k)%:R 1%N (2 ^ l * a k).
  by rewrite /exp_quo expr1 CratrE /= CratrE.
rewrite -exp_quo_plus ?ler0n // ?muln_gt0 ?a_pos ?expn_gt0 // .
rewrite [(2^l.+1)%N]expnS -mulnA.
set m := (2^l * a k)%N.
have Hm : (0 < m)%N.
  by rewrite muln_gt0 a_pos expn_gt0.
apply: exp_quo_equiv; last first.
- rewrite -mulnDl -expnS.
  rewrite mulnAC !mulnA.
  do 4 congr (_ * _)%N.
  suff -> : (2 ^ l.+1 - 2 + 1 = 2 ^ l.+1 - 1)%N.
    rewrite mulnBl expnS mulnC.
      by congr (_ * 2 - _)%N.
    rewrite addn1 -subSn ?subSS // .
    by rewrite expnS -[2]muln1 leq_mul // ?expn_gt0 // .
- by rewrite ler0n.
- by rewrite muln_gt0 Hm.
- by rewrite muln_gt0 Hm.
Qed.

Lemma w_seq_bound_tail k (Hk : (2 <= k)%N) l :
  w_seq (k + l) <= w_seq k * (a' k) ^+ 2.
Proof.
apply: (le_trans (w_seq_bound Hk l)).
rewrite ler_pmul ?w_seq_ge0 ?exp_quo_ge0 ?ler0n ?muln_gt0 ?a_pos ?expn_gt0 // .
have -> : a' k ^+ 2 = exp_quo (a k)%:Q 2%N (a k).
  by rewrite /a' /exp_quo -exprM mul1n.
rewrite exp_quo_lessn // ?muln_gt0 ?expn_gt0 ?a_pos // ?ler1n ?a_pos // .
rewrite !mulnA leq_mul2r expnS.
by rewrite leq_subr orbT.
Qed.

End W_k.

(* In Maple: *)
(* > evalf(1415 / 1000 * 1443 / 1000 * 1321/1000 * 1092/1000 * (1004/1000)^2); *)
(*                                   2.969037292 *)

Definition a'0_ub : rat := rat_of_Z 283 / rat_of_Z 200.

Definition a'1_ub : rat := rat_of_Z 1443 / rat_of_Z 1000.

Definition a'2_ub : rat := rat_of_Z 1321 / rat_of_Z 1000.

Definition a'3_ub : rat := rat_of_Z 273 / rat_of_Z 250.

Definition a'4_ub : rat := rat_of_Z 201 / rat_of_Z 200.

End A'.

(* Reported to survive end of section *)
Hint Resolve a'_ge0.
Hint Resolve a'_gt0.
Hint Resolve a'_gt1.

Module Computations.

(* Can't be moved before *)
(* Import ZArith. *)

Hint Resolve rat_of_Z_Zpos.

(* Missing from rat_of_Zpos *)
Lemma rat_of_Z_ZposW z : 0 <= rat_of_Z (Zpos z).
Proof. exact: ltW. Qed.

Lemma rat_of_Z_of_nat n : rat_of_Z (Z.of_nat n) = n%:~R.
Proof.
rewrite rat_of_ZEdef /=; case: n => [| n] //=.
by rewrite /rat_of_Z_ /rat_of_Z_fun SuccNat2Pos.id_succ.
Qed.

Lemma rat_of_Z_pow z n : rat_of_Z (z ^ Z.of_nat n) = (rat_of_Z z) ^ n.
Proof.
rewrite -Zpower_nat_Z; elim: n => [| n ihn].
- by rewrite expr0z Zpower_nat_0_r -rat_of_Z_1.
rewrite Zpower_nat_succ_r; case: rat_morph_Z => _ _ _ _ -> _ _.
by rewrite ihn -[RHS]exprnP exprS exprnP.
Qed.

Hint Resolve rat_of_Z_ZposW.

Definition w : rat := a'0_ub * a'1_ub * a'2_ub * a'3_ub * a'4_ub ^ 2.

Lemma w_val : w = rat_of_Z (5949909309448377) / rat_of_Z (2 * (10 ^ 15))%coqZ.
Proof.
rewrite /w /a'0_ub /a'1_ub /a'2_ub /a'3_ub /a'4_ub.
rat_field.
by (do ! split);
  apply/eqP; rewrite -rat_of_ZEdef extra_mathcomp.lt0r_neq0 //.
Qed.

Lemma w_gt0 : 0 < w. Proof.  rewrite w_val divr_gt0 //; exact: rat_of_Z_Zpos. Qed.

Lemma w_ge0 : 0 <= w. Proof. apply: ltW; exact: w_gt0. Qed.

Lemma w_lt3 : w < 3%:~R.
Proof.
rewrite w_val ltr_pdivr_mulr ?rat_of_Z_Zpos // -subr_gt0.
have -> : 3%:~R * rat_of_Z (2 * 10 ^ 15) - rat_of_Z 5949909309448377 =
          rat_of_Z (3 * 2 * 10 ^ 15 - 5949909309448377).
  rat_field.
set p := (X in 0 < rat_of_Z X).
vm_compute in p; apply: rat_of_Z_Zpos.
Qed.

Lemma w_gt1 : (1 < w).
Proof.
rewrite w_val ltr_pdivl_mulr ?rat_of_Z_Zpos // 1?mul1r -subr_gt0.
set v := (X in rat_of_Z X - _).
set w := (X in _ - rat_of_Z X).
have ->: rat_of_Z v - rat_of_Z w = rat_of_Z (v - w) by rat_field.
set p := (X in 0 < rat_of_Z X).
vm_compute in p; apply: rat_of_Z_Zpos.
Qed.

Hint Resolve w_gt1.

Section PosNum.
Context {R : numFieldType}.
Lemma posrat (r : {posnum rat}) : 0 < (ratr (num_of_pos r) : R).
Proof. by rewrite ltr0q; case:r.  Qed.

End PosNum.

(* Computer-algebra aided proof. *)
Lemma w_upper_bounded k : w_seq k <= w%:C.
Proof.
wlog le4k : k / (4 <= k)%nat.
  move=> hwlog; case: (leqP 4 k) => [|ltk4]; first exact: hwlog.
  apply: le_trans (hwlog 4 _) => //; apply: w_seq_incr; exact: ltnW.
rewrite -(subnK le4k) addnC; apply: le_trans (w_seq_bound_tail _ _) _ => //.
have -> : w_seq 4 = a' 0 * a' 1 * a' 2 * a' 3.
  by rewrite /w_seq !big_ord_recr /= big_ord0 mul1r.
have a'0_ubP : a' 0 <= a'0_ub%:C.
  have gt0a0 : (0 < a 0)%nat by apply: a_pos.
  have ge0a'0 : 0 <= a'0_ub%:C by rewrite ler0q divr_ge0.
  apply: root_le_x => //. 
  rewrite -rmorphX ler_rat /a'0_ub exprMn exprVn lter_pdivl_mulr ?exprn_gt0 //.
  rewrite a0. 
  (*goal:   2%:~R * rat_of_Z 200 ^+ 2 <= rat_of_Z 283 ^+ 2: the length of
    the proof is ridiculous... *)
  set aval := (X in (Posz X)%:~R * _ ^+ X <= _ ^+ X).
  set p := (X in _ * (rat_of_Z X) ^+ _ <= _);
  set q := (X in _ * _ <= rat_of_Z X ^+ _).
  rewrite -subr_ge0 !exprnP; set rhs := (X in 0 <= X).
  pose pos := (q ^ Z.of_nat aval - Z.of_nat aval * p ^ Z.of_nat aval)%coqZ.
  have -> : rhs = rat_of_Z pos.
  rewrite /rhs /pos. (* this should be enough unfolding, but requires morphism lemmas on
   rat_of_Z. For now, we do computations twice. *)
  rewrite /aval /p /q; rat_field.
  suff -> : pos = 89%coqZ by exact: rat_of_Z_ZposW.
    done.
  have a'1_ubP : a' 1 <= a'1_ub%:C.
  have gt0a0 : (0 < a 1)%nat by apply: a_pos.
  have ge0a'1 : 0 <= a'1_ub%:C by rewrite ler0q divr_ge0.
  apply: root_le_x=> //. 
  rewrite -rmorphX ler_rat /a'1_ub exprMn exprVn lter_pdivl_mulr ?exprn_gt0 //.
  rewrite a1.
  set aval := (X in (Posz X)%:~R * _ ^+ X <= _ ^+ X).
  set p := (X in _ * (rat_of_Z X) ^+ _ <= _);
  set q := (X in _ * _ <= rat_of_Z X ^+ _).
  rewrite -subr_ge0 !exprnP; set rhs := (X in 0 <= X).
  pose pos := (q ^ Z.of_nat aval - Z.of_nat aval * p ^ Z.of_nat aval)%coqZ.
  have -> : rhs = rat_of_Z pos.
    rewrite /rhs /pos. (* this should be enough unfolding, but requires morphism lemmas on
   rat_of_Z. For now, we do computations twice. *)
    rewrite /aval /p /q [Z.of_nat _]/=; rat_field.
    suff -> : pos = 4685307%coqZ by exact: rat_of_Z_ZposW.
    done.
have a'2_ubP : a' 2 <= a'2_ub%:C.
   have ge0a'1 : 0 <= a'2_ub%:C by rewrite ler0q divr_ge0.
   have ge0a2 : 0 <= ratr (a 2)%:~R :> algC by rewrite ler0q.
   suff step : ratr (a 2)%:~R <= ratr a'2_ub ^+ a 2 :> algC.
     exact: root_le_x.
  (* below to be improved *)
  rewrite -rmorphX ler_rat /a'1_ub exprMn exprVn lter_pdivl_mulr ?exprn_gt0 //.
  rewrite a2.
  set aval := (X in (Posz X)%:~R * _ ^+ X <= _ ^+ X).
  set p := (X in _ * (rat_of_Z X) ^+ _ <= _);
  set q := (X in _ * _ <= rat_of_Z X ^+ _).
  rewrite -subr_ge0 !exprnP; set rhs := (X in 0 <= X).
  pose pos := (q ^ Z.of_nat aval - Z.of_nat aval * p ^ Z.of_nat aval)%coqZ.
  have -> : rhs = rat_of_Z pos.
    rewrite /rhs /pos. (* this should be enough unfolding, but requires morphism lemmas on
   rat_of_Z. For now, we do computations twice. *)
    rewrite /aval /p /q [Z.of_nat _]/=; rat_field.
    suff -> : pos = 19718930047012279641%coqZ by exact: rat_of_Z_ZposW.
    by vm_compute.
have a'3_ubP : a' 3 <= a'3_ub%:C.
  have gt0a0 : (0 < a 3)%nat by apply: a_pos.
  have ge0a'1 : 0 <= a'3_ub%:C by rewrite ler0q divr_ge0.
  have ge0a3 : 0 <= ratr (a 3)%:~R :> algC by rewrite ler0q.
  suff step : ratr (a 3)%:~R <= ratr a'3_ub ^+ a 3 :> algC.
   exact: root_le_x.
  rewrite -rmorphX ler_rat /a'1_ub exprMn exprVn lter_pdivl_mulr; last first.
    by rewrite exprn_gt0.
  rewrite a3.
  set aval := (X in (Posz X)%:~R * _ ^+ X <= _ ^+ X).
  set p := (X in _ * (rat_of_Z X) ^+ _ <= _);
  set q := (X in _ * _ <= rat_of_Z X ^+ _).
  rewrite -subr_ge0 !exprnP; set rhs := (X in 0 <= X).
  pose pos := (q ^ Z.of_nat aval - Z.of_nat aval * p ^ Z.of_nat aval)%coqZ.
  have -> : rhs = rat_of_Z pos.
    rewrite /rhs /pos. (* this should be enough unfolding, but requires morphism lemmas on
   rat_of_Z. For now, we do computations twice. *)
    rewrite /aval /p /q [Z.of_nat _]/=; rat_field.
    suff -> : pos = 13082865684162319442059723917554130432970820125555268741037120404410598256687652105894050330796735063217%coqZ by exact: rat_of_Z_ZposW.
    by vm_compute.
have a'4_ubP : a' 4 <= a'4_ub%:C.
  have gt0a0 : (0 < a 4)%nat by apply: a_pos.
  have ge0a'1 : 0 <= a'4_ub%:C by rewrite ler0q divr_ge0.
  have ge0a4 : 0 <= ratr (a 4)%:~R :> algC by rewrite ler0q ler0z.
  suff step : ratr (a 4)%:~R <= ratr a'4_ub ^+ a 4 :> algC.
   exact: root_le_x.
  pose t : rat := (rat_of_Z 200)^-1.
  have t_gt0 : 0 < t by rewrite /t invr_gt0 rat_of_Z_Zpos. 
  have t_ge0 : 0 <= t by exact: ltW.
  have -> : a'4_ub = 1 + t.
    by rewrite /a'4_ub /t; rat_field; move/eqP; rewrite rat_of_Z_eq0 //.
  rewrite -rmorphX ler_rat a4 exprDn.
  suff step : 1807%:~R <= \sum_(i < 8) 1 ^+ (1807 - i) * t ^+ i *+ 'C(1807, i).
    have -> : (1808 = 8 + 1800)%N by [].
    rewrite big_split_ord /=; apply: ler_paddr; last by [].
    apply: sumr_ge0 => [] [i hi] _ /=; rewrite expr1n mul1r pmulrn_lge0. 
      by apply: exprn_ge0 => //. 
    by rewrite bin_gt0 -[1807]/(1799 + 8)%N leq_add2l.
  pose f k := t ^+ k *+ 'C(1807, k).
  have bump0n i : bump 0 i = i.+1 by rewrite /bump /= add1n.
  do 8! (rewrite big_ord_recl /= expr1n mul1r -/(f _) ?bump0n).
  rewrite big_ord0. set lhs := (X in _ <= X).
  suff -> : lhs = (rat_of_Z 34077892883014859211)/ rat_of_Z 12800000000000000.
    rewrite lter_pdivl_mulr; last exact: rat_of_Z_Zpos.
    rewrite -rat_of_Z_of_nat rat_of_ZEdef -rat_of_Z_mul -subr_ge0 -rat_of_Z_sub.
    set x := (X in rat_of_Z_ X). compute in x.
    rewrite -rat_of_ZEdef; exact: rat_of_Z_ZposW.
  rewrite /lhs /f bin0 mulr1n bin1 expr0 expr1.
  have -> : t ^+ 7 *+ 'C(1807, 7) =  t ^+ 7 * rat_of_Z 12337390971384003811.
    rewrite -mulr_natr. congr (_ * _). rewrite -mulrz_nat natz.
    rewrite -binz_nat_nat binzE // 7!factS.
    set x := 1800`!.
    set d := (X in X / _).
    suff -> : d =
       (rat_of_Z (1807 * (1806 * (1805 * (1804 * (1803 * (1802 * (1801)))))))) * x%:~R.
      have : x%:~R <> 0 :> rat.
        move/eqP; apply/negP; rewrite intr_eq0 eqz_nat /x; apply: lt0n_neq0.
        exact: fact_gt0.
      move: x {d} => x hx.  
      set f7 := (X in _ / (X * _)).
      have -> : f7 = rat_of_Z 5040 by rewrite /f7 -rat_of_Z_of_nat. 
      rat_field. split; first by []. move/eqP; rewrite rat_of_Z_eq0; done. 
    have {d}-> : d = (1807 * 1806 * 1805 * 1804 * 1803 * 1802 * 1801)%N%:~R * x%:~R.
       rewrite -[_%:~R * x %:~R]intrM /d; apply/eqP; rewrite eqr_int.
       by set u := 1801; move: u {d} x => u x; rewrite -PoszM -!mulnA.
    congr (_ * x%:~R);  rewrite -rat_of_Z_of_nat. 
    set l := (X in rat_of_Z X = _).
    set r := (X in _ = rat_of_Z X).
    suff -> : l = r by []. 
    by rewrite {}/l {}/r !Nat2Z.inj_mul.
  have -> : t ^+ 6 *+ 'C(1807, 6) = t ^+ 6 * rat_of_Z 47952102609488077.
    rewrite -mulr_natr. congr (_ * _). rewrite -mulrz_nat natz.
    rewrite -binz_nat_nat binzE // 6!factS.
    set x := 1801`!.
    set d := (X in X / _).
    suff -> : d =
       (rat_of_Z (1807 * (1806 * (1805 * (1804 * (1803 * (1802))))))) * x%:~R.
      have : x%:~R <> 0 :> rat.
        move/eqP; apply/negP; rewrite intr_eq0 eqz_nat /x; apply: lt0n_neq0.
        exact: fact_gt0.
      move: x {d} => x hx.  
      set f6 := (X in _ / (X * _)).
      have -> : f6 = rat_of_Z 720 by rewrite /f6 -rat_of_Z_of_nat. 
      rat_field. split; first by []. move/eqP; rewrite rat_of_Z_eq0; done. 
    have {d}-> : d = (1807 * 1806 * 1805 * 1804 * 1803 * 1802)%N%:~R * x%:~R.
       rewrite -[_%:~R * x %:~R]intrM /d; apply/eqP; rewrite eqr_int.
       by set u := 1802; move: u {d} x => u x; rewrite -PoszM -!mulnA.
    congr (_ * x%:~R);  rewrite -rat_of_Z_of_nat. 
    set l := (X in rat_of_Z X = _).
    set r := (X in _ = rat_of_Z X).
    suff -> : l = r by []. 
    by rewrite {}/l {}/r !Nat2Z.inj_mul.
  have -> : t ^+ 5 *+ 'C(1807, 5) =  t ^+ 5 * rat_of_Z 159662938766331.
    rewrite -mulr_natr. congr (_ * _). rewrite -mulrz_nat natz.
    rewrite -binz_nat_nat binzE // 5!factS.
    set x := 1802`!.
    set d := (X in X / _).
    suff -> : d =
       (rat_of_Z (1807 * (1806 * (1805 * (1804 * (1803)))))) * x%:~R.
      have : x%:~R <> 0 :> rat.
        move/eqP; apply/negP; rewrite intr_eq0 eqz_nat /x; apply: lt0n_neq0.
        exact: fact_gt0.
      move: x {d} => x hx.  
      set f5 := (X in _ / (X * _)).
      have -> : f5 = rat_of_Z 120 by rewrite /f5 -rat_of_Z_of_nat. 
      rat_field. split; first by []. move/eqP; rewrite rat_of_Z_eq0; done. 
    have {d}-> : d = (1807 * 1806 * 1805 * 1804 * 1803)%N%:~R * x%:~R.
       rewrite -[_%:~R * x %:~R]intrM /d; apply/eqP; rewrite eqr_int.
       by set u := 1803; move: u {d} x => u x; rewrite -PoszM -!mulnA.
    congr (_ * x%:~R);  rewrite -rat_of_Z_of_nat. 
    set l := (X in rat_of_Z X = _).
    set r := (X in _ = rat_of_Z X).
    suff -> : l = r by []. 
    by rewrite {}/l {}/r !Nat2Z.inj_mul.
  have -> : t ^+ 4 *+ 'C(1807, 4) = t ^+ 4 * rat_of_Z 442770212885.
    rewrite -mulr_natr. congr (_ * _). rewrite -mulrz_nat natz.
    rewrite -binz_nat_nat binzE // 4!factS.
    set x := 1803`!.
    set d := (X in X / _).
    suff -> : d =
       (rat_of_Z (1807 * (1806 * (1805 * (1804))))) * x%:~R.
      have : x%:~R <> 0 :> rat.
        move/eqP; apply/negP; rewrite intr_eq0 eqz_nat /x; apply: lt0n_neq0.
        exact: fact_gt0.
      move: x {d} => x hx.  
      set f4 := (X in _ / (X * _)).
      have -> : f4 = rat_of_Z 24 by rewrite /f4 -rat_of_Z_of_nat. 
      rat_field. split; first by []. move/eqP; rewrite rat_of_Z_eq0; done. 
    have {d}-> : d = (1807 * 1806 * 1805 * 1804)%N%:~R * x%:~R.
       rewrite -[_%:~R * x %:~R]intrM /d; apply/eqP; rewrite eqr_int.
       by set u := 1804; move: u {d} x => u x; rewrite -PoszM -!mulnA.
    congr (_ * x%:~R);  rewrite -rat_of_Z_of_nat. 
    set l := (X in rat_of_Z X = _).
    set r := (X in _ = rat_of_Z X).
    suff -> : l = r by []. 
    by rewrite {}/l {}/r !Nat2Z.inj_mul.
  have -> : t ^+ 3 *+ 'C(1807, 3) =
            t ^+ 3 * rat_of_Z 981752135.
    rewrite -mulr_natr. congr (_ * _). rewrite -mulrz_nat natz.
    rewrite -binz_nat_nat binzE // 3!factS.
    set x := 1804`!.
    set d := (X in X / _).
    suff -> : d = (rat_of_Z (1807 * (1806 * (1805)))) * x%:~R.
      have : x%:~R <> 0 :> rat.
        move/eqP; apply/negP; rewrite intr_eq0 eqz_nat /x; apply: lt0n_neq0.
        exact: fact_gt0.
      move: x {d} => x hx.  
      set f3 := (X in _ / (X * _)).
      have -> : f3 = rat_of_Z 6 by rewrite /f3 -rat_of_Z_of_nat. 
      rat_field. split; first by []. move/eqP; rewrite rat_of_Z_eq0; done. 
    have {d}-> : d = (1807 * 1806 * 1805)%N%:~R * x%:~R.
       rewrite -[_%:~R * x %:~R]intrM /d; apply/eqP; rewrite eqr_int.
       by set u := 1805; move: u {d} x => u x; rewrite -PoszM -!mulnA.
    congr (_ * x%:~R);  rewrite -rat_of_Z_of_nat. 
    set l := (X in rat_of_Z X = _).
    set r := (X in _ = rat_of_Z X).
    suff -> : l = r by []. 
    by rewrite {}/l {}/r !Nat2Z.inj_mul.
  have -> : t ^+ 2 *+ 'C(1807, 2) =
            t ^+ 2 * rat_of_Z 1631721.
    rewrite -mulr_natr. congr (_ * _). rewrite -mulrz_nat natz.
    rewrite -binz_nat_nat binzE // 2!factS.
    set x := 1805`!.
    set d := (X in X / _).
    suff -> : d = (rat_of_Z (1807 * (1806 ))) * x%:~R.
      have : x%:~R <> 0 :> rat.
        move/eqP; apply/negP; rewrite intr_eq0 eqz_nat /x; apply: lt0n_neq0.
        exact: fact_gt0.
      move: x {d} => x hx.  
      set f2 := (X in _ / (X * _)).
      have -> : f2 = rat_of_Z 2 by rewrite /f2 -rat_of_Z_of_nat. 
      rat_field. split; first by []. move/eqP; rewrite rat_of_Z_eq0; done. 
    have {d}-> : d = (1807 * 1806)%N%:~R * x%:~R.
       rewrite -[_%:~R * x %:~R]intrM /d; apply/eqP; rewrite eqr_int.
       by set u := 1806; move: u {d} x => u x; rewrite -PoszM -!mulnA.
    congr (_ * x%:~R);  rewrite -rat_of_Z_of_nat. 
    set l := (X in rat_of_Z X = _).
    set r := (X in _ = rat_of_Z X).
    suff -> : l = r by []. 
    by rewrite {}/l {}/r !Nat2Z.inj_mul.
  have -> : t *+ 1807 = t * rat_of_Z 1807. 
    rewrite -mulr_natr; congr (_ * _).
    by rewrite -mulrz_nat natz -rat_of_Z_of_nat. 
  rewrite /t !exprnP. rat_field.
  by split; move/eqP; rewrite rat_of_Z_eq0.
have {a'4_ubP} a'4_ubP :  a' 4 ^+ 2 <=  (a'4_ub ^ 2)%:C.
  by rewrite  CratrE /= exprSr expr1 ler_pmul ?a'_ge0.
rewrite /w 4!rmorphM /=; do 4! (rewrite ler_pmul ?mulr_ge0 ?a'_ge0 //).

Qed.

End Computations.

Import Computations.

(* change name to make it not seem general *)
Lemma prod_is_exp_sum (n k : nat) (tenn : rat := (10 * n)%nat%:~R) :
  \prod_(i < k.+1) exp_quo tenn (a i).-1 (a i) =
  tenn%:C ^+ k * exp_quo tenn 1 (a k.+1 - 1).
Proof.
elim: k => [|k ihk]; first by rewrite expr0 big_ord_recr big_ord0 /= !mul1r.
have pos_tenn : 0 <= tenn by rewrite /tenn ler0n.
have h l : tenn%:C ^+ l = exp_quo tenn l 1.
  by rewrite -exp_quo_r_nat; repeat (rewrite -CratrE /=).
rewrite h -exp_quo_plus 1?subn_gt0 ?a_gt1 //.
rewrite big_ord_recr [a _]lock /= -lock.
have side : (0 < a k.+1 - 1)%nat by rewrite subn_gt0.
rewrite ihk h -!exp_quo_plus // mul1n // [a k.+1]aS !subn1 /=.
congr exp_quo; ring.
Qed.

Hint Resolve w_ge0.
Hint Resolve w_gt0.
Hint Resolve w_seq_ge0.

Hint Resolve aS_gt2.

Lemma aSpred_gt1 k : (1 < (a k.+1).-1)%nat.
by rewrite -subn1 ltn_subRL addn1.
Qed.

Hint Resolve aSpred_gt1.

Lemma aR_gt0 i : 0 < ((a i)%:~R : algC).
Proof.
by rewrite ltr0n.
Qed.

Lemma aR_ge0 i : 0 <= ((a i)%:~R : algC).
Proof.
by rewrite ler0n.
Qed.

Hint Resolve aR_gt0.
Hint Resolve aR_ge0.

Section PreliminaryRemarksTheorem2.

(* We lost the %N delimiter for ssrnat operations *)
Lemma remark_t2_1 n k (Hank : (a k <= n < (a k.+1))%nat) :
  (expn n n)%:Q%:C <= n%:Q%:C * exp_quo n%:Q (n * (a k.+1).-2) ((a k.+1).-1).
Proof.
have HnaSk : (n <= (a k.+1).-1)%nat.
    by rewrite -ltnS; case/andP: Hank.
have n_ge1 : (1 <= n)%nat.
  case/andP: Hank => H1 _.
  apply: leq_trans; first exact (a_pos 0).
  by apply: leq_trans H1; rewrite a_grows.
have lt1sSk : (0 < ((a k.+1).-1))%nat.
  by rewrite -subn1 subn_gt0 a_gt1.
have lt2sSk : (0 < ((a k.+1).-2))%nat.
  by rewrite -subn2 subn_gt0 aS_gt2.
rewrite -{3}[n]expn1 !exp_quo_nat_nat.
rewrite -exp_quo_plus // ?ler0n //. 
have -> : exp_quo n%:~R n 1 = exp_quo n%:~R (n * ((a k.+1).-1)) ((a k.+1).-1).
  by apply: exp_quo_equiv; rewrite ?ler0n ?muln1.
rewrite muln1 mul1n; apply: exp_quo_lessn; rewrite ?ler1n // .
suff Hinterm :
  ((n + n * (a k.+1).-2) <= ((a k.+1).-1 + n * (a k.+1).-2))%nat.
  apply: leq_mul => // .
  have {1}-> : ((a k.+1).-1 = (a k.+1).-2 + 1)%nat.
    by rewrite -[in RHS]subn1 subnK.
  rewrite addnC mulnDr leq_add 1?muln1 //.
exact: leq_add.
Qed.

Lemma remark_t2_2 k1: 
  \prod_(i < k1) exp_quo (a i)%:~R (a i).-1 (a i) =
 (\prod_(i < k1) (a i)%:~R) / w_seq k1.
  elim: k1 => [|k1 HIk1].
    by rewrite /w_seq !big_ord0 invr1 mulr1.
  rewrite /w_seq 3!big_ord_recr /= HIk1 -!mulrA -/(w_seq k1).
  congr (_ * _).
  rewrite invrM 1?unitf_gt0 ?w_seq_gt0 ?a'_gt0 // .
  rewrite mulrA mulrAC -mulrA mulrC -!mulrA; congr (_ * _).
  rewrite /a' /exp_quo -rootCV ?ler0q ?ler0n // .
  rewrite -subn1 GRing.exprB 1?rootCK 1?mulrC 1?CratrE /= 1?CratrE /=
                 ?unitf_gt0 ?rootC_gt0 ?ltr0n ?a_pos // ; congr (_ * _).
  by rewrite rootCV -1?exprVn ?ler0n; try (exact: isT).
Qed.

End PreliminaryRemarksTheorem2.

Theorem t2 n k (Hank : (a k <= n < (a k.+1))%nat) :
  (C n k.+1)%:Q%:C < exp_quo (10%:Q * n%:Q) (2*k.+1 - 1) 2 * (w%:C ^+ n.+1).
Proof.
have n_ge1 : (1 <= n)%nat.
  case/andP: Hank => H1 _.
  apply: leq_trans; first exact (a_pos 0).
  by apply: leq_trans H1; rewrite a_grows.
have lt0nC : 0 < n%:Q%:C.
  by rewrite ltr0q ltr0n.
have le0nR : 0 <= n%:~R :> rat.
  by rewrite ler0n.
have le0nC : 0 <= ratr n%:~R :> algC.
  by rewrite ler0q le0nR.
have n_unit :  n%:Q%:C \is a GRing.unit.
  by rewrite unitf_gt0 //.
have H10_ge1 : 1 <= 10%:Q * n%:~R.
  by rewrite mulr_ege1 ?ler1n.
have Hprod := (prod_is_exp_sum n k).
have l10 := (l10 (proj1 (andP Hank))).
move: 10%nat H10_ge1 Hprod l10 => ten H10_ge1 Hprod l10.
have H10n_ge0 : 0 <= ten%:Q * n%:Q by rewrite mulr_ge0 ?ler0n.
set cn := (C _ _)%:Q%:C; set t10n_to := exp_quo (ten%:Q * n%:Q).
have Hexp_1_aS_ge0 : 0 <= t10n_to 1%nat (a k.+1).-1.
  by rewrite exp_quo_ge0.
have t_pos a b : (0 < b)%nat -> 0 <= t10n_to a b.
  by move=> hb; rewrite /t10n_to; apply: exp_quo_ge0.
have wq_ge0 m : 0 <= w%:C ^+ m by rewrite exprn_ge0 // ler0q.
have wq_gt0 m : 0 < w%:C ^+ m by rewrite exprn_gt0 // ltr0q.
suff step1 : cn <  t10n_to (2 * k.+1 - 1)%nat 2 * w%:C ^+ n * w_seq k.+1.
apply: lt_le_trans step1 _; rewrite -mulrA; apply: ler_pmul => //.
  + exact: t_pos.
  + apply: mulr_ge0 => //; exact: wq_pos.
  + by rewrite exprSr ler_pmul // w_upper_bounded.
rewrite -mulrA; set tw := (X in _ < _ * X).
have tw_pos : 0 <= tw by rewrite /tw; apply: mulr_ge0.
have tenn_to_pos : (0 : algC) <= ratr ((ten%:~R * n%:~R) ^+ k).
  by rewrite ler0q exprn_ge0.
suff step2 : cn < ((ten%:Q * n%:Q) ^+ k)%:C *
       t10n_to 1%nat ((a k.+1).-1)%nat * tw.
  apply: lt_le_trans step2 _; apply: ler_pmul => // .
  - by apply: mulr_ge0 => //; apply: t_pos.
  - have step2_1 : t10n_to 1%nat (a k.+1).-1 <=
           t10n_to 1%nat 2.
      by rewrite exp_quo_lessn // !mul1n.
    have -> : t10n_to (2 * k.+1 - 1)%nat 2 =
              t10n_to (k)%nat 1%nat * t10n_to (1)%nat 2.
      rewrite -exp_quo_plus //; apply:exp_quo_equiv => // .
      by rewrite  -[k.+1]addn1 mulnDr addn2 subn1 /= [(k * 2)%nat]mulnC addn1.
    by apply: ler_pmul => // ; rewrite exp_quo_r_nat.
have -> : tw =
          ratr w ^+ n * n%:Q%:C * (w_seq k.+1 / n%:Q%:C).
  by rewrite [_ / _]mulrC mulrA mulrC -mulrA divrr // /tw mulr1 mulrC.
have Helper0 :  (0 : algC) < \prod_(i < k.+1) (a i)%:~R.
  by rewrite prodr_gt0.
have Helper1 : (\prod_(i < k.+1) (a i)%:~R : algC) \is a GRing.unit.
  by rewrite unitf_gt0 //.
have Helper2 :  0 < \prod_(i < k.+1) a' i.
  by rewrite prodr_gt0.
have Helper3 : (\prod_(i < k.+1) a' i) \is a GRing.unit.
  by rewrite unitf_gt0 //.
have Helper4 : (\prod_(i < k.+1) a' i)^-1 \is a GRing.unit.
  by rewrite GRing.unitrV.
have step3 : (w_seq k.+1 / ratr n%:~R) >=
             (\prod_(i < k.+1) exp_quo (a i)%:~R (a i).-1 (a i))^-1.
  rewrite remark_t2_2 /w_seq invrM // invrK .
  rewrite ler_pdivr_mulr // -mulrA ler_pmulr // mulrC ler_pdivl_mulr // mul1r.
  case/andP: Hank => _; rewrite a_rec => H; rewrite -prodMz.
  rewrite CratrE /= CratrE /= ler_nat.
  by rewrite big_mkord addn1 ltnS in H.
have ler0_10npow : 0 <= ratr ((ten%:~R * n%:~R) ^+ k) *
                        t10n_to 1%nat (a k.+1).-1.
  by rewrite mulr_ge0.
have t_ge0_0 : 0 <= \prod_(i < k.+1) exp_quo (a i)%:~R (a i).-1 (a i).
  by rewrite prodr_ge0 // => i _; rewrite exp_quo_ge0 // ler0n.
have t_ge0_1 : 0 <= (\prod_(i < k.+1) exp_quo (a i)%:~R (a i).-1 (a i))^-1.
  by rewrite invr_ge0.
have t_ge0_2 : (0 : algC) <= ratr w ^+ n * ratr n%:~R.
  rewrite mulr_ge0 //.
have t_ge0_3 : 0 <=
   ratr w ^+ n * ratr n%:~R /
   \prod_(i < k.+1) exp_quo (a i)%:~R (a i).-1 (a i).
  by rewrite mulr_ge0 // invr_ge0.

have t_ge0_4 :  0 < exp_quo n%:~R (n * (a k.+1).-2) (a k.+1).-1.
  by rewrite exp_quo_gt0 // ltr0n.
have t_ge0_5 :  0 < (exp_quo n%:~R (n * (a k.+1).-2) (a k.+1).-1)^-1.
  by rewrite invr_gt0.
have t_ge0_6 : (0 : algC) <= ratr (n ^ n)%nat%:~R.
  by rewrite ler0q ler0n.
have t_ge0_7 :   0 <= ratr w ^+ n *
   (ratr (n ^ n)%nat%:~R / exp_quo n%:~R (n * (a k.+1).-2) (a k.+1).-1) /
   \prod_(i < k.+1) exp_quo (a i)%:~R (a i).-1 (a i).
  by rewrite mulr_ge0 // mulr_ge0 // mulr_ge0 // invr_ge0 // ltW.
have t_ge0_8 : 0 <= (w_seq k.+1) ^+ n.
  by rewrite exprn_ge0.
have t_ge0_9 :    0 <=
   w_seq k.+1 ^+ n *
   (ratr (n ^ n)%nat%:~R / exp_quo n%:~R (n * (a k.+1).-2) (a k.+1).-1).
  by rewrite mulr_ge0 // divr_ge0 // exp_quo_ge0 // ler0n.
have t_ge0_10 :    0 <=
   w_seq k.+1 ^+ n *
   (ratr (n ^ n)%nat%:~R / exp_quo n%:~R (n * (a k.+1).-2) (a k.+1).-1) /
   \prod_(i < k.+1) exp_quo (a i)%:~R (a i).-1 (a i).
  by rewrite mulr_ge0 // mulr_ge0 // ltrW // .
have Hbound :
  (expn n n)%:Q%:C / exp_quo n%:Q (n * (a k.+1).-2)%nat ((a k.+1).-1) <= n%:Q%:C.
  by rewrite ler_pdivr_mulr //; exact: (remark_t2_1 Hank).

suff step4 : cn < ratr ((ten%:~R * n%:~R) ^+ k) * t10n_to 1%nat (a k.+1).-1 *
   ((w_seq k.+1) ^+ n *
    ((n ^ n)%nat%:Q%:C / exp_quo n%:Q (n * (a k.+1).-2)%nat ((a k.+1).-1)) /
    (\prod_(i < k.+1) exp_quo (a i)%:~R (a i).-1 (a i))).
  apply: lt_le_trans step4 _. apply: ler_pmul => // .
  apply: ler_pmul => // .
  apply: ler_pmul => // ; first by rewrite mulr_ge0 // ltW.
rewrite ler_expn2r //.
  by rewrite nnegrE.
  by rewrite nnegrE ler0q.
  exact: w_upper_bounded.
have other_prod_is_exp_sum k1 : \prod_(i < k1.+1) exp_quo (n%:~R) n (a i)
          = exp_quo n%:~R (n * (a k1.+1).-2) (a k1.+1).-1.
  elim: k1 => [|k1 HIk1].
    by rewrite big_ord_recr big_ord0 /= mul1r muln1; congr exp_quo.
  rewrite  [a _.+1]lock big_ord_recr /= -lock HIk1 -exp_quo_plus //=; last first.
    by rewrite muln_gt0; apply/andP.
  apply: exp_quo_equiv => //=.
  - by rewrite muln_gt0 andbT muln_gt0; apply /andP.
  - by rewrite muln_gt0 /= muln_gt0; apply/andP.
  set x := (a k1 * (a k1).-1).-1%nat.
  have -> : (a k1 * ((a k1).-1) = x.+1)%nat.
    by rewrite /x prednK // muln_gt0; apply/andP.
  have -> /= : ((x.+2 * x.+1) = (x^2 + 3*x).+2)%nat by ring.
    (* This call to ring fails if we do not confine the previous 
'Import ZArith' in a module... *)
   ring.
rewrite -other_prod_is_exp_sum.
rewrite /t10n_to.
have -> :
  ratr ((ten%:~R * n%:~R) ^+ k) * exp_quo (ten%:~R * n%:~R) 1 (a k.+1).-1 =
  \prod_(i < k.+1) exp_quo (ten%:~R * n%:~R) (a i).-1 (a i).
 rewrite -rmorphM /= Hprod; congr (_ * _).
   by rewrite !CratrE /= .
 by rewrite subn1.
set rhs := (X in _ < X).
suff Hfinal : rhs = (n ^ n)%nat%:Q %:C *
\prod_(i < k.+1) exp_quo (ten%:Q * n%:Q / (a i)%:Q) (a i).-1 (a i) /
\prod_(i < k.+1) exp_quo (n%:Q / (a i)%:Q) n (a i).
  rewrite Hfinal {Hfinal}.
  case/andP: Hank => Hle Hlt.
  exact: l10.
rewrite /rhs /w_seq.
rewrite mulrAC [ratr (n ^ n)%nat%:~R / _]mulrC 2!mulrA.
rewrite -[in RHS]mulrA [in RHS]mulrC .
congr (_ * ratr (n ^ n)%nat%:~R).
rewrite [_ ^+ n / _]mulrC mulrA.
have ai_pos i : 0 < (a i)%:~R by rewrite ltr0n.
have ai_ge0 i : 0 <= (a i)%:~R by rewrite ler0n.
have ->: \prod_(i < k.+1) exp_quo (ten%:~R * n%:~R) (a i).-1 (a i) /
          \prod_(i < k.+1) exp_quo (a i)%:~R (a i).-1 (a i) =
          \prod_(i < k.+1) exp_quo (ten%:~R * n%:~R / (a i)%:~R) (a i).-1 (a i).
  rewrite -prodf_div; apply: eq_bigr => i _.
  have en0 : exp_quo (a i)%:~R (a i).-1 (a i) != 0.
    by rewrite eq_sym; apply: ltr_neq; apply: exp_quo_gt0.
  apply: (canLR (mulfK en0)).
  by rewrite exp_quo_mult_distr // mulfVK // eq_sym ltr_neq.
rewrite -mulrA; congr (_ * _).
rewrite -2!prodfV -prodrXl -big_split /=; apply: eq_bigr => i _.
rewrite -[a' i ^+ n]invrK -invfM.
rewrite -exp_quo_mult_distr; last by rewrite invr_ge0.
rewrite -exprVn /a' /exp_quo -rootCV // ?ler0q //.
set x := _.-root _; set y := _.-root _.
by rewrite CratrE /= -/x mulrC.
Qed.


Theorem t2_rat n k (Hank : (a k <= n < (a k.+1))%nat) :
  (C n k.+1)%:Q < (10%:Q * n%:Q) ^ k.+1 * (w ^+ n.+1).
Proof.
suff : ratr (C n k.+1)%:~R <
            exp_quo (10%:~R * n%:~R) (2 * k.+1) 2 * ratr w ^+ n.+1.
  by rewrite /exp_quo exprM sqrtCK -!rmorphX /= -rmorphM /= ltr_rat.
have {Hank} t2 := t2 Hank.
apply: lt_le_trans t2 _; apply: ler_pmul => //.
- apply: exp_quo_ge0; first by [].
  by apply: mulr_ge0; exact:ler0z.
- by apply: exprn_ge0; rewrite ler0q.
case: n => [| n]; first by rewrite mulr0 !exp_quo_0 /= mulnC muln2.
apply: exp_quo_lessn=> //; first by rewrite -rmorphM /= -[1]/(1%:~R) ler_nat.
by rewrite leq_mul2r leq_subr orbT.
Qed.

Lemma w_ge1 : (1 <= w).
Proof. apply: ltW. exact: w_gt1. Qed.

Hint Resolve w_ge1.

Lemma better_k_bound n k (Hank : (a k <= n < (a k.+1))%nat) :
  (k <= trunc_log 2 (trunc_log 2 n) + 2)%nat.
Proof.
case: k Hank => [| k] //; case: k => [| k Hank]; last exact: k_bound.
by rewrite addn2.
Qed.

Delimit Scope nat_scope with ssrN.

Theorem t3_nat : exists (K : nat),
    (0 < K)%nat /\ forall n : nat, (iter_lcmn n <= K * 3 ^ n)%nat.
Proof.
pose cond n k := (a k <= n < (a k.+1))%nat.
suff [K [Kpos KP]] : exists (K : nat),
    (0 < K)%nat /\ (forall n k, cond n k -> C n k.+1 <=  K * 3 ^ n)%nat.
  exists K; split => // n; case: (leqP n 1)=> hn; last first.
    apply: leq_trans (KP _ (f_k n) _); first exact: lcm_leq_Cnk.
    exact: n_between_a.
  case: n hn => [_ | n]; first by rewrite expn0 muln1 iter_lcmn0.
  by case: n => // _; rewrite iter_lcmn1 expn1 muln_gt0 Kpos.
suff [K [Kpos KP]] : exists K : rat,
    (0 < K) /\ forall n k, cond n k -> (C n k.+1)%:R <=  K * 3%:R ^ n.
  have := floorQ_spec K.
  move/floorQ_ge0: (ltW Kpos); case: (floorQ K) => k // _ /andP[_ leKSn].
  exists k.+1; split=> // n m /KP {KP} KP.
  suff: (C n m.+1)%:R <= (k%:~R + 1) * 3%:R ^ n :> rat.
    by rewrite -[_ + 1%:R]natrD -[_ ^ n]natrX -natrM ler_nat addn1.
  apply: le_trans KP _. apply: ler_wpmul2r; (* booo *) first exact: exprz_ge0.
  exact: ltW.
pose m : rat := locked 10%:~R.
have lt0m : 0 < m by rewrite /m -lock.
have le0m : 0 <= m by exact: ltW.
have lt1m : 1 < m by rewrite /m -lock.
have le1m : 1 <= m by exact: ltW.
have mE : m = 10%:~R by rewrite /m -lock.
pose eps : rat := locked (w / 3%:R).
have epsE : eps = w / 3%:R by rewrite /eps -lock.
have lt0eps1 : 0 < eps < 1.
  by rewrite epsE ltr_pdivl_mulr // mul0r ltr_pdivr_mulr // mul1r w_lt3 w_gt0.
pose u n k eps := (m * n%:R) ^ k.+1 * eps ^ n.+1 : rat.
suff hloglog : exists (K : rat), (0 < K) /\ (forall n k, cond n k -> u n k eps < K).
  have [K [lt0K KP]] := hloglog.
  exists (K * 3%:~R); split; first by exact: mulr_gt0.
  move=> n k hcond.
  apply: le_trans (ltW (t2_rat hcond)) _; rewrite -mulrA -exprSz.
  rewrite -ler_pdivr_mulr; last by exact: exprz_gt0.
  rewrite -mulrA -expr_div_n -mE -epsE; apply: ltW; exact: KP.
have [lt0eps  lteps1] := andP lt0eps1.
pose loglog n := trunc_log 2 (trunc_log 2 n).
pose v n : rat := (m * n%:R) ^ (loglog n).+3 * eps ^ n.+1.
have le0v n : 0 <= v n.
  by rewrite /v pmulr_lge0 ?exprz_gt0 // exprz_ge0 // mulr_ge0 // ler0n.
suff {u} [K [Kpos KP]] : exists K : rat, 0 < K /\ forall n, v n < K.
  exists K; split => // n k /better_k_bound hkn; apply: le_lt_trans (KP n).
  rewrite /u /v ler_pmul2r; last by apply: exprz_gt0.
  case: n hkn => [| n] hkn; first by rewrite mulr0 !exp0rz.
  apply: exp_incr_expp; first by apply: mulr_ege1=> //; rewrite ler1n.
  by rewrite ltnS -addn2.
have h1 n : ((trunc_log 2 n).+1 <= 2 ^ (loglog n).+1)%nat by exact: trunc_log_ltn.
have {h1} h1 n : (n < 2 ^ (2 ^ (loglog n).+1))%nat.
  have h : (n < 2 ^ (trunc_log 2 n).+1)%nat by exact: trunc_log_ltn.
  have {h} h : (2 ^ (trunc_log 2 n).+1 <= 2 ^ (2 ^ (loglog n).+1))%nat by rewrite leq_exp2l.
  apply: leq_trans h; exact: trunc_log_ltn.
have h2 n : (1 < n)%nat -> (2 ^ (2 ^ (loglog n)) <= n)%nat.
  move=> lt1n.
  have lt0n : (0 < n)%nat by apply: ltn_trans lt1n.
  have h : (2 ^ (trunc_log 2 n) <= n)%nat by apply: trunc_logP.
  apply: leq_trans h; rewrite leq_exp2l // /w; apply: trunc_logP=> //.
  by apply: trunc_log_max.
pose y n := (2 ^ 2 ^ (loglog n).+1)%nat; pose x n := (2 ^ 2 ^ (loglog n))%nat.
pose t n := (m * (y n)%:R) ^ (loglog n).+3 * eps ^ (x n).+1.
have le0y n : 0 <= (y n)%:R :> rat by rewrite ler0n.
suff {v le0v} [K [Kpos KP]] : exists K : rat, 0 < K /\ forall n, t n < K.
  pose KK := K + v 0%N + v 1%N.
  have lt0KK : 0 < KK by rewrite /KK  -addrA ltr_spaddl // addr_ge0. 
  have ltKKK : K <= KK by rewrite /KK -addrA ler_addl addr_ge0.
  have ltvKK n : (n <= 1)%N -> v n < KK.
     rewrite leq_eqVlt ltnS leqn0; case/orP=> /eqP->; rewrite /KK.
     - by rewrite cpr_add ltr_spaddl.
     - by rewrite addrAC  cpr_add ltr_spaddl.
  exists KK; split => // n. 
  case: (leqP n 1%N)=> [le1n | lt1n]; first exact: ltvKK. 
  apply: lt_le_trans ltKKK.
  apply: le_lt_trans (KP n); rewrite /v /t.
  (* use case for posreal-style automation... *)
  apply: ler_pmul.
  - apply: exprz_ge0; rewrite pmulr_rge0 //; exact: ler0n.
  - by apply: exprz_ge0; apply: ltW.
  - apply: ler_expn2r; last first.
      apply: ler_wpmul2l=> //; rewrite ler_nat ltnW //; exact: h1.
      + by rewrite rpredM // rpred_nat.
      + by rewrite rpredM // rpred_nat.
  - by apply: exp_incr_expn=> //; rewrite /x ltnS; apply: h2.
pose u n := (m * (x n)%:R) ^+ (2 * (loglog n).+3) * eps ^ (x n).
suff {t y le0y} [K [Kpos KP]] : exists K : rat, 0 < K /\ forall n, u n < K.
  exists K; split => // n. apply: le_lt_trans (KP n); rewrite {KP} /u /t.
  apply: ler_pmul.
  - by apply: exprz_ge0; rewrite pmulr_rge0 // ler0n.
  - by apply: exprz_ge0; apply: ltW.
  -  rewrite exprnP PoszM -exprz_exp; apply: ler_expn2r.
     + by apply: rpredM => //; apply: rpred_nat.
     + by apply: rpredX; apply: rpredM => //; apply: rpred_nat.
  - rewrite expfzMl; apply: ler_pmul=> //;  first by apply: ler_eexpr.
    by rewrite -exprnP -natrX ler_nat /x /y expnS mulnC expnM.
  - rewrite -exprnP exprSr; apply: ler_pimulr; last by apply: ltW.
    apply: exprn_ge0; exact: ltW.
have {h2} h2 n : (1 < n)%N -> (x n <= n)%N by apply: h2.
pose alpha n := (2 ^ 2 ^ n)%nat.
have le0alpha n : 0 <= (alpha n)%:R :> rat by rewrite ler0n.
have lt_0_alpha n : (0 < alpha n)%nat by rewrite /alpha expn_gt0.
pose t n := (m * (alpha n)%:R) ^ (2 * n.+3)%:Z * eps ^ alpha n.
have lt_0_t n : 0 < t n.
  rewrite /t; apply: mulr_gt0; apply: exprz_gt0=> //.
  by apply: mulr_gt0 => //; rewrite ltr0n.
have le_0_t n : 0 <= t n by exact: ltW.
suff {x h1 h2 u} [K [Kpos KP]] : exists K : rat, 0 < K /\ forall n, t n < K.
  by exists K; split => // n; apply: le_lt_trans (KP (loglog n)).
pose l n := (alpha n)%:R ^ 4 * eps ^ ((alpha n)%:Z ^ 2 - 2%:Z * (alpha n)%:Z).
have alphaS n : (alpha n.+1 = (alpha n) ^ 2)%nat.
  by rewrite /alpha expnS mulnC expnM.
have le_0_alpham2 k : 0 <= (alpha k)%:Z - 2%:Z.
  rewrite /alpha; apply: (@le_trans _ _ ((2 ^ 2 ^ 0)%:Z - 2%:Z)) => //.
  by apply: ler_sub=> //; rewrite lez_nat leq_exp2l // leq_exp2l.
have maj_t n : t n.+1 <= (t n) ^ 2 * (l n).
  rewrite /t 2!expfzMl !exprz_exp expfzMl -2!mulrA -[_ * _ * l n]mulrA.
  apply: ler_pmul; first exact: exprz_ge0. (* missing posreal... *)
  - apply: mulr_ge0; apply: exprz_ge0 => //; exact: ltW.
  - apply: exp_incr_expp => //.
    by rewrite -mulnA leq_pmul2l -[X in (X < _)%nat]muln1 // ltn_pmul2l.
    rewrite /l mulrCA 2!mulrA -exprzD_nat -mulrA -expfzDr; last exact: lt0r_neq0.
    apply: ler_pmul; first exact: exprz_ge0. (* missing posreal... *)
    - apply: exprz_ge0; exact: ltW.
    - rewrite alphaS natrX exprnP exprz_exp; apply: exp_incr_expp.
        by rewrite -[1]/(1%:R) ler_nat /alpha expn_gt0.
      have -> : (4 + 2 * n.+3 * 2 = 2 * (2 + n.+3 * 2))%nat by rewrite mulnDr mulnA.
      by rewrite leq_mul2l //= -[_.+4]addn1 addnC mulnDr [(_ * _.+3)%nat]mulnC.
    - set a := (X in _ <= eps ^ X).
      have -> : a = (alpha n ^ 2)%:Z by rewrite /a addrCA mulrC addrN addr0.
      by rewrite alphaS.
have le_0_l n : 0 <= l n. 
  rewrite /l; apply: mulr_ge0; first by apply/exprz_ge0/ler0n.  
  by apply/exprz_ge0/ltW.
case: rat_morph_Z => m0 m1 madd msub mmul mopp _.
pose eps1 := locked (rat_of_Z 5949909309448377). 
(* Import ZArith. *)
pose eps2 := locked (rat_of_Z ( 6 * (10 ^ 15))%coqZ).
have lt0eps2 : 0 < eps2 by rewrite /eps2 -lock; exact: rat_of_Z_Zpos. 
have eps2_val : eps2 = 3%:R * rat_of_Z (2 * 10 ^ 15).
  rewrite /eps2 -lock -[6%coqZ]/(3%coqZ * 2%coqZ)%coqZ -Z.mul_assoc mmul. 
  by rewrite -[3%coqZ]/(Z.of_nat 3) rat_of_Z_of_nat. 
have epsF : eps = eps1 / eps2.
  by rewrite /eps -lock eps2_val invfM [RHS]mulrA [RHS]mulrAC w_val /eps1 -lock.
have a3 : (alpha 3 = (expn 2 8)) by [].
have lt_l3_1 : l 3%ssrN <= 1.
  have -> : l 3%nat = (2%:R * eps ^ (2%:R ^ 3 * ((alpha 3)%:R - 2%:R))) ^ (2 ^ 5)%ssrN%:R.
    rewrite expfzMl -exprnP -natrX. set x := _%:R ^ _%:R.
    have  -> : x = (alpha 3)%:R ^ 4 :> rat.
      rewrite -exprnP -natrX {}/x natz -exprnP -natrX.
      set x := (X in X%:R = _). set y := (X in _ = X%:R).
(*        (* rewrite [x]lock; rewrite [y]lock. congr (_%:R). stack overflow *) *)
      suff -> : x = y by move: x y. 
      by rewrite {}/x {}/y a3 -expnM; congr (expn _  _). 
    by rewrite  exprz_exp /l; congr (_ * eps ^ _). (* slow line *)
  rewrite expr_le1 //; last by rewrite pmulr_rge0 // exprz_ge0 //; exact: ltW.
  have small_calc : 2%:R * eps ^ 90%N <= 1.
     rewrite epsF expfzMl mulrA -expfV ler_pdivr_mulr; last exact: exprz_gt0.
     rewrite mul1r -subr_ge0.
     have -> : eps2 ^ 90%ssrN - 2%:R * eps1 ^ 90%N = rat_of_Z
     ((BinInt.Z.pow (6 * 10 ^ 15) 90) - 2 * (BinInt.Z.pow 5949909309448377 90)).
       rewrite msub mmul -[90%coqZ]/(Z.of_nat 90) !rat_of_Z_pow; congr (_ - _).
       - by rewrite /eps2 -lock.
       - by rewrite -[2%coqZ]/(Z.of_nat 2) rat_of_Z_of_nat /eps1 -lock.
    vm_compute; exact: rat_of_Z_ZposW.
  apply: le_trans small_calc. rewrite ler_pmul2l; last by [].
  by rewrite ler_piexpz2l.
rewrite [l]lock in lt_l3_1.
have lt_t4_1 : t 4%nat < 1.
  rewrite {l le_0_l lt_l3_1 maj_t loglog a3}.
  pose a4 := locked alpha 4.
  have lt0a4 : (0 < a4)%ssrN by rewrite /a4 -lock.
  have -> : t 4 = (m * a4%:R) ^ 14 * eps ^ alpha 4 by rewrite /t /a4 -lock.
  suff [M hM]: exists2 M, (M * 14 <= alpha 4)%ssrN & (m * a4%:R) * eps ^ M < 1.
    move=> hm.
    have {hm} : (m * a4%:R) ^14 * eps ^ (M * 14)%ssrN < 1.
      rewrite PoszM -exprz_exp -expfzMl; apply: exprn_ilt1=> //.
      rewrite -mulrA pmulr_rge0 // pmulr_rge0 ?ltr0n //; apply: exprz_ge0; exact: ltW.
    apply: le_lt_trans. rewrite ler_pmul2l; first by rewrite ler_piexpz2l.
    by apply: exprz_gt0; rewrite pmulr_rgt0 // ltr0n.   
  pose e := rat_of_Z 992 / rat_of_Z (10 ^ 3).
  have ltepse : eps < e.
    rewrite epsF ltr_pdivr_mulr // /e mulrAC ltr_pdivl_mulr; last  exact: rat_of_Z_Zpos.
    have -> : eps2 = rat_of_Z (6 * 10 ^ 12) * rat_of_Z (10 ^ 3).
      by rewrite -[RHS]mmul /eps2 -Z.mul_assoc -Zpower_exp // mmul -lock.
    rewrite mulrA ltr_pmul2r ?rat_of_Z_Zpos // -[X in _ < X]mmul.
    rewrite -subr_gt0 /eps1 -lock -[X in 0 < X]msub.
    exact: rat_of_Z_Zpos. (* long *)
  suff [M le14M]: exists2 M, (M * 14 <= alpha 4)%ssrN &  (m * a4%:R) * (e ^ M) < 1.
    move=> hm; exists M => //; apply: le_lt_trans hm. rewrite ler_pmul2l; last first.
      by rewrite pmulr_rgt0 // ltr0n.
    apply: ler_wpexpz2r=> //; apply: ltW=> //.
    rewrite /e divr_gt0 //; exact: rat_of_Z_Zpos. 
  suff [M le14M]: exists2 M, (M * 14 <= alpha 4)%ssrN & 
      0 < (rat_of_Z (10 ^ 3)) ^ M -  (m * a4%:R) * ((rat_of_Z 992) ^ M).
     move=> hm; exists M => //.
     rewrite /e  expfzMl -expfV mulrA ltr_pdivr_mulr; last by rewrite exprz_gt0 // rat_of_Z_Zpos.
     by rewrite mul1r -subr_gt0.
  exists 2000. 
     rewrite /alpha. rewrite -subn_eq0.
     rewrite -!NatTrec.trecE.
     done.  (* FIXME : compute in Z. *)
     suff : 0 < rat_of_Z ((BinInt.Z.pow 1000 2000) - (10 * BinInt.Z.pow 2 (2 ^ 4)) * (BinInt.Z.pow 992 2000)).
       set g := (X in _ -> X).
       rewrite msub mmul -[2000%coqZ]/(Z.of_nat 2000) !rat_of_Z_pow mmul {}/g.
       set x := (X in 0 < X -> _). set y := (X in _ -> 0 < X).
       suff -> : x = y by [].
       rewrite {}/x {}/y. set x := (X in _ - X = _). set y := (X in _ = _ - X). 
       suff -> : x = y by [].
       rewrite {}/x {}/y. 
       suff [-> ->] :  rat_of_Z (2 ^ 2 ^ 4) = a4%:R /\ rat_of_Z 10 = m by [].
       rewrite -[10%coqZ]/(Z.of_nat 10) -[(2 ^ 4)%coqZ]/(Z.of_nat (2 ^4)) rat_of_Z_pow.
       rewrite -[2%coqZ]/(Z.of_nat 2) !rat_of_Z_of_nat; split; last by [].
       by rewrite /a4 -lock /alpha natrX; congr (_ ^+ _).
  vm_compute; exact: rat_of_Z_Zpos.
rewrite [t]lock in lt_t4_1.
have lt_ln_1 (n : nat) : (3 <= n)%ssrN -> l n <= 1.
  elim: n => [// | n ihn].
  rewrite leq_eqVlt; case/orP=> [/eqP<- | /ihn {ihn} ihn]; first by rewrite [l]lock. (* unlock does not work... *)
  suff h : l n.+1 <= (l n) ^ 2 by apply: le_trans h _; apply: mulr_ile1.
  rewrite /l expfzMl exprz_exp; apply: ler_pmul.
  - apply: exprz_ge0; exact: ler0n.

  - apply: exprz_ge0; exact: ltW.
  - by rewrite alphaS natrX exprnP exprz_exp.
  rewrite exprz_exp; apply: ler_wpiexpz2l.
  - exact: ltW.
  - exact: ltW.

  - rewrite -topredE /= -mulrBl; apply: mulr_ge0; last by [].
    exact: le_0_alpham2.
  - rewrite -topredE /= -mulrBl; apply: mulr_ge0; last by [].
    exact: mulr_ge0.
  - rewrite alphaS -subr_ge0; set a := alpha _; set x := (X in 0 <= X); set az := a%:Z.
    have {x} -> : x = az ^+ 2 ^+ 2 - (2%:Z * az) ^+ 2 + 4%:Z * az.
      rewrite /x -!addrA; congr (_ + _); rewrite [_ * 2%:Z]mulrC.
      by rewrite  mulrBr opprD opprK addrA -opprD -mulrDl exprMn mulrA. (* missing ring...*)
    rewrite subr_sqr; apply: addr_ge0; last by apply: mulr_ge0.
    apply: mulr_ge0; last by apply: addr_ge0.
    rewrite expr2 -mulrBl; apply: mulr_ge0; last by [].
    exact: le_0_alpham2.
suff [K [lt0K [N Pn]]] : exists K : rat,  0 < K /\ exists N : nat, (forall n, (N < n)%nat -> t n < K).
  (* a bigenough would be nice here *)
  pose KK := (K + \sum_(0 <= j < N.+1) t j).
  have le0sum : 0 <= \sum_(0 <= j < N.+1) t j by apply: sumr_ge0=> n _; exact: ltW.
  have lt0KK : 0 < KK by rewrite /KK; apply: ltr_spaddl. 
  have ltKK : K <= KK by rewrite /KK ler_addl.
  have KKmaj j : (j <= N)%nat -> t j < KK.
    move=> lej4; rewrite /KK (bigD1_seq j) //=; last by rewrite mem_iota iota_uniq.
    - rewrite addrA addrAC cpr_add; apply: ltr_spaddl=> //; apply: sumr_ge0=> n _; exact: ltW.
    by rewrite mem_index_iota.
  exists KK; split => [|] //; elim=> [| n ihn]; first exact: KKmaj.
  case: (ltnP n.+1 N.+1) => [lenN | ltNn]; first exact: KKmaj.
  by apply: lt_le_trans ltKK; apply: Pn.
exists 1; split => //; exists 3; elim=> [| n ihn] //. 
rewrite leq_eqVlt; case/orP=> [/eqP<- | lt3n]; first by rewrite [t]lock.
have {ihn} ihn := ihn lt3n.
apply: le_lt_trans (maj_t _) _; apply: (@le_lt_trans _ _ (t n ^ 2)); last first.
  by apply: mulr_ilt1.
rewrite ger_pmulr; first by apply: lt_ln_1; rewrite ltnS in lt3n; apply: ltn_trans lt3n.
exact: exprz_gt0.
Qed.



Theorem t3 : exists (K : nat),
    (0 < K)%nat /\
    forall n, (iter_lcmn n)%:Q <= (K * expn 3 n)%nat%:Q.
Proof.
have [K [Kpos Kmaj]] := t3_nat.
by exists K; split => // n; rewrite ler_nat.
Qed.

End Hanson.
