Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_field.
Require Import extra_mathcomp tactics binomialz floor arithmetics posnum.
Require Import rat_of_Z hanson_elem_arith hanson_elem_analysis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

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

Module Hanson.

Section PreliminaryRemarksLemma7.

Variables (n i : nat).
Hypothesis Hain : (a i <= n)%N.

Lemma remark_7_1 : (n.+1 - a i <= n %/ a i * a i)%N.
Proof. by rewrite leq_subLR -mulSn ltn_ceil. Qed.

Lemma remark_7_2 :
  exp_quo ((n.+1 - a i)%N%:Q / (a i)%:Q) (n.+1 - a i) (a i) <=
  ((n %/ a i) ^ (n %/ a i))%N%:Q%:C.
Proof.
rewrite exp_quo_nat_nat; apply: exp_quo_self_grows => //.
- by rewrite divr1.
- by rewrite divr_gt0 // ltr0n subn_gt0.
- by rewrite ler1n divn_gt0.
by rewrite ler_pdivr_mulr // -natrM ler_nat remark_7_1.
Qed.

Lemma remark_7_3 :
  let f := fun u => exp_quo (u / (a i)%:Q) in
  f n%:Q n (a i) / ((n %/ a i) ^ (n %/ a i))%N%:Q%:C <=
  f n%:Q n (a i) / f (n.+1 - a i)%N%:Q (n.+1 - a i)%N (a i).
Proof.
rewrite /= ler_pdivr_mulr; last first.
  by rewrite ltr0q ltr0n expn_gt0 divn_gt0 ?Hain.
rewrite[X in _ <= X]mulrC mulrA ler_pdivl_mulr.
- rewrite mulrC; apply/ler_wpmul2l/remark_7_2.
  by apply: exp_quo_ge0; rewrite // divr_ge0 ?ler0n.
- by apply: exp_quo_gt0; rewrite // divr_gt0 // ltr0n ?subn_gt0.
Qed.

(* This one would ideally be entirely automated *)
Lemma remark_7_4 :
  let r := (a i - 1)%N%:Q / (n.+1 - a i)%N%:Q in
  (exp_quo (n%:Q / (a i)%:Q) n (a i) /
           exp_quo ((n.+1 - a i)%N%:Q / (a i)%:Q) (n.+1 - a i) (a i)) ^+ a i =
  exp_quo (1 + r) (n.+1 - a i) (a i) ^+ a i *
  ((n%:Q / (a i)%:Q) ^ (a i - 1)%N)%:C.
Proof.
move => r.
have {r} ->: 1 + r = n%:Q / (n.+1 - a i)%N%:Q.
  by rewrite /r -!subzn //; first field; ring_lia.
case: (a i) (a_pos i) Hain => // ai' _ Hain'.
rewrite subn1 subSS exprMn exprVn ![exp_quo _ _ _ ^+ ai'.+1]exprAC !rootCK //.
rewrite rmorphX !rmorphM !fmorphV !rmorph_int !exprMn !exprVn !exprnP /=.
rewrite -subzn ?expfzDr -?invr_expz ?exprz_pintl; [| ring_lia..].
by field; rewrite !intr_eq0 !expf_eq0; lia.
Qed.

End PreliminaryRemarksLemma7.

(* Notation "2" := 2%:R : ring_scope. *)


(* TODO rename + chainage avant *)
Lemma l7 n i (Hain : (a i <= n)%N) :
  exp_quo (n%:Q / (a i)%:Q) n (a i) / ((n %/ a i) ^ (n %/ a i))%N%:Q%:C <
  exp_quo (10%N%:Q * n%:Q / (a i)%:Q) (a i - 1) (a i).
Proof.
have posai_rat : 0 < (a i)%:Q by rewrite ltr0n.
pose posai := PosNumDef posai_rat.
have -> : (a i)%:Q = num_of_pos posai by [].
have lt0n : (0 < n)%N by exact: leq_trans Hain.
have lt0n_rat : 0 < n%:Q by rewrite ltr0n.
pose posn := PosNumDef lt0n_rat.
have -> : n%:Q = num_of_pos posn by [].
apply: le_lt_trans (remark_7_3 Hain) _.
set lhs := (X in X < _); set rhs := (X in _ < X).
suff : lhs ^+ a i < rhs ^+ a i.
  rewrite ltr_pexpn2r // nnegrE; last exact: exp_quo_ge0.
  (* roots, hence alg. numbers prevent using posnum based automation *)
  by rewrite /lhs divr_ge0 // exp_quo_ge0 // divr_ge0 // ler0z.
rewrite remark_7_4 // /rhs -mulrA ![_ ^+ _ ^+ a i]exprAC !rootCK //.
rewrite rmorphD rmorphX 15!(rmorph1, rmorph_int, rmorphM, fmorphV) /=.
rewrite [(10%:~R * _) ^+ _]exprMn ltr_pmul2r ?exprn_gt0 ?divr_gt0 ?ltr0n //.
set x := (n.+1 - a i)%N.
set y := (a i - 1)%N.
rewrite -root_lt_x ?exprn_ge0 ?addr_ge0 ?divr_ge0 ?ler0n ?subn_gt0 //.
have: 9%:~R < 10%:~R :> algC by rewrite ltr_nat.
have/one_plus_invx_expx: 0 < x%:~R / y%:~R :> rat.
  by rewrite divr_gt0 // ltr0n subn_gt0.
rewrite /exp_quo rmorphD rmorphM fmorphV !rmorph1 !rmorph_int.
by rewrite rootCX ?addr_ge0 ?divr_ge0 ?ler0n ?subn_gt0 //; exact: le_lt_trans.
Qed.


(* First inequality on C *)
Lemma l10 n k (Hank : (a k <= n)%N) :
  (C n k.+1)%:Q%:C <
  (n ^ n)%N%:Q%:C *
  \prod_(i < k.+1) exp_quo (10%:Q * n%:Q / (a i)%:Q) (a i).-1 (a i) /
  \prod_(i < k.+1) exp_quo (n%:Q / (a i)%:Q) n (a i).
Proof.
have lt0n : (0 < n)%N by exact: leq_trans (a_pos k) _.
have Hinterm : (C n k.+1)%:~R <=
    ((n ^ n)%N%:~R / (\prod_(i < k.+1) (n %/ a i) ^ (n %/ a i))%N%:~R) :> algC.
  rewrite ler_pdivl_mulr.
    by move: (l8 n k.+1); rewrite big_mkord mulrC -natrM ler_nat.
  by rewrite ltr0n prodn_gt0 // => i; rewrite expn_gt0; case: (n %/ a i)%N.
rewrite !ratr_int -mulrA; apply: le_lt_trans Hinterm _.
rewrite ltr_pmul2l ?ltr0n ?expn_gt0 ?lt0n //= ltr_pdivl_mulr; last first.
  apply: prodr_gt0 => i _.
  by rewrite exp_quo_gt0 ?divr_ge0 ?divr_gt0 ?ltr0n ?a_pos.
rewrite prodMz /= mulrC -prodf_div.
apply: ltr_prod; first by apply/hasP; exists ord0; rewrite // mem_index_enum.
move=> [i /= Hi] _; rewrite divr_ge0 ?exp_quo_ge0 ?a_pos ?divr_ge0 ?ler0n //=.
suff/l7: (a i <= n)%N by rewrite !CratrE subn1.
exact/leq_trans/Hank/a_grows.
Qed.

Section A'.

Implicit Types i : nat.

Definition a' i : algC := exp_quo (a i)%:Q 1%N (a i).

Lemma a'_gt0 i : 0 < a' i. Proof. by rewrite rootC_gt0 ?CratrE ?ltr0n. Qed.
Hint Resolve a'_gt0 : core.

Lemma a'_ge0 i : 0 <= a' i. Proof. exact: ltW. Qed.
Hint Resolve a'_ge0 : core.

Lemma a'_gt1 i : 1 < a' i.
Proof. by rewrite exprn_egte1 // rootC_gt1 ?ltr1q ?ltr1n. Qed.
Hint Resolve a'_gt1 : core.

Lemma a'_S i (Hi : (2 <= i)%N) : a' i.+1 <= sqrtC (a' i).
Proof.
have /andP[H1 H2] := Observation_compare_a_a i.
rewrite /a' /exp_quo !expr1 !CratrE root_le_x -?rootCX ?rootC_ge0 ?ler0n //.
rewrite root_x_le ?rootC_ge0 ?root_x_le ?exprn_ge0 ?ler0n //.
rewrite -!natrX ler_nat -expnM.
have/leq_trans -> //: (a i.+1 ^ (2 * a i) <= a i ^ (2 * (2 * a i)))%N.
  by rewrite [(a i ^ _)%N]expnM leq_exp2r ?(ltnW H2) // muln_gt0 /=.
rewrite leq_exp2l //; apply: leq_trans (ltnW H1).
rewrite -lez_nat -subr_ge0 -subn1 !PoszM -subzn //.
set rhs := (X in 0 <= X).
have -> : rhs = (a i)%:Z * ((a i)%:Z - 6%:Z) + 1 by lia.
rewrite addr_ge0 // mulr_ge0 // subr_ge0.
exact/leq_trans/a_grows/Hi.
Qed.

Lemma a'_bound i j (Hi : (2 <= i)%N) : a' (i + j) <= (2 ^ j).-root (a' i).
Proof.
elim: j => [|j HIj] //.
  by rewrite addn0 expn0 root1C.
rewrite addnS.
have /a'_S Ha : (2 <= i + j)%N by apply: (leq_trans Hi); rewrite leq_addr.
apply: le_trans Ha _; rewrite expnS prod_root ?expn_gt0 //.
by rewrite ler_rootC ?nnegrE // rootC_ge0 ?expn_gt0.
Qed.

Section W_k.

Definition w_seq k := \prod_(i < k) a' i.

Lemma w_seq_gt0 k : 0 < w_seq k.
Proof. by rewrite prodr_gt0 // => i _ ; exact:a'_gt0. Qed.

Lemma w_seq_ge0 k : 0 <= w_seq k.
Proof. exact/ltW/w_seq_gt0. Qed.

Lemma w_seq_le_S k : w_seq k <= w_seq k.+1.
Proof.
rewrite /w_seq big_ord_recr /=.
by rewrite ler_pmulr 1?ltW ?a'_gt1 // prodr_gt0 // => i _.
Qed.

Lemma w_seq_incr k l : (k <= l)%N -> w_seq k <= w_seq l.
Proof.
elim: l => [|l ihl]; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt ltnS; case/predU1P => [-> // | /ihl hkl].
exact: le_trans (w_seq_le_S _).
Qed.


Lemma w_seq_bound k (Hk : (2 <= k)%N) l :
  w_seq (k + l) <= w_seq k * exp_quo (a k)%:Q (2 ^ l.+1 - 2) (2 ^ l * a k).
Proof.
elim: l => [|l HIl].
  by rewrite addn0 /= expn1 subnn /= /exp_quo expr0 mulr1.
rewrite addnS /w_seq big_ord_recr /=.
suff -> : exp_quo (a k)%:Q (2 ^ l.+2 - 2) (2 ^ l.+1 * a k) =
          exp_quo (a k)%:Q (2 ^ l.+1 - 2) (2 ^ l * a k) * (2 ^ l).-root (a' k).
  rewrite mulrA.
  apply: ler_pmul; rewrite ?a'_bound // ?rootC_ge0 ?CratrE ?a_pos ?ler0n //.
  by rewrite prodr_ge0 // => i _ ; exact: a'_ge0.
rewrite -prod_root ?CratrE ?expn_gt0 ?a_pos ?ler0n //.
have -> : (2 ^ l * a k).-root (a k)%:R = exp_quo (a k)%:R 1 (2 ^ l * a k).
  by rewrite /exp_quo expr1 2!CratrE.
rewrite -exp_quo_plus ?ler0n // ?muln_gt0 ?a_pos ?expn_gt0 //.
rewrite [(2 ^ l.+1)%N]expnS -mulnA -mulnDl -subnA ?leq_pmulr ?expn_gt0 //=.
set m := (2 ^ l * a k)%N.
apply: exp_quo_equiv; last first.
- by rewrite mulnACA [in RHS]mulnBl -expnS -expnSr.
- by rewrite ler0n.
- by rewrite !muln_gt0 ?a_pos ?expn_gt0.
- by rewrite !muln_gt0 ?a_pos ?expn_gt0.
Qed.

Lemma w_seq_bound_tail k (Hk : (2 <= k)%N) l :
  w_seq (k + l) <= w_seq k * a' k ^+ 2.
Proof.
apply: le_trans (w_seq_bound Hk l) _; rewrite ler_wpmul2l ?w_seq_ge0 //.
have -> : a' k ^+ 2 = exp_quo (a k)%:Q 2 (a k).
  by rewrite /a' /exp_quo -exprM mul1n.
rewrite exp_quo_lessn // ?muln_gt0 ?expn_gt0 ?a_pos // ?ler1n ?a_pos //.
by rewrite !mulnA leq_mul2r expnS leq_subr orbT.
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
#[export] Hint Resolve a'_gt0 : core.
#[export] Hint Resolve a'_ge0 : core.
#[export] Hint Resolve a'_gt1 : core.
#[export] Hint Resolve w_seq_ge0 : core.

Module Computations.

(* Can't be moved before *)
(* Import ZArith. *)

Definition w : rat := a'0_ub * a'1_ub * a'2_ub * a'3_ub * a'4_ub ^ 2.

Lemma w_val : w = rat_of_Z 5949909309448377 / rat_of_Z (2 * 10 ^ 15).
Proof.
rewrite /w /a'0_ub /a'1_ub /a'2_ub /a'3_ub /a'4_ub.
by field.
Qed.

Lemma w_gt0 : 0 < w. Proof. by rewrite w_val divr_gt0 // rat_of_Z_Zpos. Qed.

Lemma w_ge0 : 0 <= w. Proof. exact/ltW/w_gt0. Qed.

Lemma w_lt3 : w < 3%:Q.
Proof.
rewrite w_val ltr_pdivr_mulr ?rat_of_Z_Zpos // -subr_gt0.
have -> : 3%:Q * rat_of_Z (2 * 10 ^ 15) - rat_of_Z 5949909309448377 =
          rat_of_Z (3 * 2 * 10 ^ 15 - 5949909309448377).
  ring.
by rewrite rat_of_ZEdef ltr0z.
Qed.

Lemma w_gt1 : 1 < w.
Proof.
rewrite w_val ltr_pdivl_mulr ?rat_of_Z_Zpos // 1?mul1r -subr_gt0.
by rewrite -rmorphB rat_of_Z_Zpos.
Qed.

Lemma w_ge1 : 1 <= w. Proof. exact/ltW/w_gt1. Qed.

Section PosNum.
Context {R : numFieldType}.
Lemma posrat (r : {posnum rat}) : 0 < ratr (num_of_pos r) :> R.
Proof. by rewrite ltr0q. Qed.

End PosNum.

(* Computer-algebra aided proof. *)
Lemma w_upper_bounded k : w_seq k <= w%:C.
Proof.
wlog le4k : k / (4 <= k)%N.
  move=> hwlog; case: (leqP 4 k) => [|ltk4]; first exact: hwlog.
  apply: le_trans (hwlog 4%N _) => //; apply: w_seq_incr; exact: ltnW.
rewrite -(subnK le4k) addnC; apply: le_trans (w_seq_bound_tail _ _) _ => //.
have -> : w_seq 4 = a' 0 * a' 1 * a' 2 * a' 3.
  by rewrite /w_seq !big_ord_recr /= big_ord0 mul1r.
have a'0_ubP : a' 0 <= a'0_ub%:C.
  have ge0a'0 : 0 <= a'0_ub%:C by rewrite ler0q divr_ge0.
  rewrite root_le_x // a0 -rmorphX ler_rat exprMn exprVn.
  rewrite lter_pdivl_mulr ?exprn_gt0 // -subr_ge0 mulrzl.
  by rewrite -!rmorphX -rmorphMz -rmorphB /= rat_of_ZEdef ler0z.
have a'1_ubP : a' 1 <= a'1_ub%:C.
  have ge0a'1 : 0 <= a'1_ub%:C by rewrite ler0q divr_ge0.
  rewrite root_le_x // a1 -rmorphX ler_rat exprMn exprVn.
  rewrite lter_pdivl_mulr ?exprn_gt0 // -subr_ge0 mulrzl.
  by rewrite -!rmorphX -rmorphMz -rmorphB /= rat_of_ZEdef ler0z.
have a'2_ubP : a' 2 <= a'2_ub%:C.
  have ge0a'2 : 0 <= a'2_ub%:C by rewrite ler0q divr_ge0.
  have ge0a2 : 0 <= (a 2)%:Q%:C by rewrite ler0q.
  rewrite root_le_x // a2 -rmorphX ler_rat exprMn exprVn.
  rewrite lter_pdivl_mulr ?exprn_gt0 // -subr_ge0 mulrzl.
  by rewrite -!rmorphX -rmorphMz -rmorphB /= rat_of_ZEdef ler0z.
have a'3_ubP : a' 3 <= a'3_ub%:C.
  have ge0a'3 : 0 <= a'3_ub%:C by rewrite ler0q divr_ge0.
  have ge0a3 : 0 <= (a 3)%:Q%:C by rewrite ler0q.
  rewrite root_le_x // a3 -rmorphX ler_rat exprMn exprVn.
  rewrite lter_pdivl_mulr; last exact: exprn_gt0.
  rewrite -subr_ge0 mulrzl -!rmorphX -rmorphMz -rmorphB /=.
  by rewrite rat_of_ZEdef ler0z.
have a'4_ubP : a' 4 <= a'4_ub%:C.
  have ge0a'1 : 0 <= a'4_ub%:C by rewrite ler0q divr_ge0.
  have ge0a4 : 0 <= (a 4)%:Q%:C by rewrite ler0q ler0z.
  rewrite root_le_x //.
  pose t : rat := (rat_of_Z 200)^-1.
  have -> : a'4_ub = 1 + t by rewrite /a'4_ub /t; field.
  rewrite -rmorphX ler_rat a4 exprDn.
  have -> : (1808 = 8 + 1800)%N by [].
  rewrite big_split_ord /=; apply: ler_paddr.
    apply: sumr_ge0 => i.
    by rewrite expr1n mul1r mulrn_wge0 ?exprn_ge0 ?invr_ge0.
  rewrite 8!big_ord_recl big_ord0 !expr1n !mul1r /= /bump !add1n.
  set lhs := (X in _ <= X).
  suff -> : lhs = rat_of_Z 34077892883014859211 / rat_of_Z 12800000000000000.
    have ->: 1807%:~R = rat_of_Z 1807 by rewrite rat_of_ZEdef; congr _%:~R.
    by rewrite lter_pdivl_mulr // -subr_ge0 -rmorphM -rmorphB rat_of_Z_ZposW.
  rewrite {}/lhs bin0 mulr1n bin1 expr0 expr1.
  have -> : t ^+ 7 *+ 'C(1807, 7) =  t ^+ 7 * rat_of_Z 12337390971384003811.
    rewrite -mulr_natr pmulrn -binz_nat_nat binzE_ffact -ffactnn ffactE /=.
    rewrite -!rat_of_Z_of_nat !Nat2Z.inj_mul.
    by do !(set x := Z.of_nat _; compute in x; rewrite {}/x); field.
  have -> : t ^+ 6 *+ 'C(1807, 6) = t ^+ 6 * rat_of_Z 47952102609488077.
    rewrite -mulr_natr pmulrn -binz_nat_nat binzE_ffact -ffactnn ffactE /=.
    rewrite -!rat_of_Z_of_nat !Nat2Z.inj_mul.
    by do !(set x := Z.of_nat _; compute in x; rewrite {}/x); field.
  have -> : t ^+ 5 *+ 'C(1807, 5) =  t ^+ 5 * rat_of_Z 159662938766331.
    rewrite -mulr_natr pmulrn -binz_nat_nat binzE_ffact -ffactnn ffactE /=.
    rewrite -!rat_of_Z_of_nat !Nat2Z.inj_mul.
    by do !(set x := Z.of_nat _; compute in x; rewrite {}/x); field.
  have -> : t ^+ 4 *+ 'C(1807, 4) = t ^+ 4 * rat_of_Z 442770212885.
    rewrite -mulr_natr pmulrn -binz_nat_nat binzE_ffact -ffactnn ffactE /=.
    rewrite -!rat_of_Z_of_nat !Nat2Z.inj_mul.
    by do !(set x := Z.of_nat _; compute in x; rewrite {}/x); field.
  have -> : t ^+ 3 *+ 'C(1807, 3) = t ^+ 3 * rat_of_Z 981752135.
    rewrite -mulr_natr pmulrn -binz_nat_nat binzE_ffact -ffactnn ffactE /=.
    rewrite -!rat_of_Z_of_nat !Nat2Z.inj_mul.
    by do !(set x := Z.of_nat _; compute in x; rewrite {}/x); field.
  have -> : t ^+ 2 *+ 'C(1807, 2) = t ^+ 2 * rat_of_Z 1631721.
    rewrite -mulr_natr pmulrn -binz_nat_nat binzE_ffact -ffactnn ffactE /=.
    rewrite -!rat_of_Z_of_nat !Nat2Z.inj_mul.
    by do !(set x := Z.of_nat _; compute in x; rewrite {}/x); field.
  by rewrite /t; field.
by rewrite 4!rmorphM rmorphX /=; do 4!rewrite ler_pmul ?mulr_ge0 //.
Qed.

End Computations.

Import Computations.

#[export] Hint Resolve w_gt0 : core.
#[export] Hint Resolve w_ge0 : core.

(* change name to make it not seem general *)
Lemma prod_is_exp_sum (n k : nat) (tenn := (10 * n)%N%:Q) :
  \prod_(i < k.+1) exp_quo tenn (a i).-1 (a i) =
  tenn%:C ^+ k * exp_quo tenn 1 (a k.+1 - 1).
Proof.
elim: k => [|k ihk]; first by rewrite expr0 big_ord_recr big_ord0.
have pos_tenn : 0 <= tenn by rewrite /tenn ler0n.
have h l : tenn%:C ^+ l = exp_quo tenn l 1 by rewrite -exp_quo_r_nat -!CratrE.
rewrite big_ord_recr ihk /= !h !subn1 -!exp_quo_plus ?ltnS ?muln_gt0 ?a_pos //=.
congr exp_quo; lia.
Qed.

Lemma aR_gt0 i : 0 < (a i)%:~R :> algC.
Proof. by rewrite ltr0n. Qed.

Lemma aR_ge0 i : 0 <= (a i)%:~R :> algC.
Proof. by rewrite ler0n. Qed.

#[export] Hint Resolve aR_gt0 : core.
#[export] Hint Resolve aR_ge0 : core.

Section PreliminaryRemarksTheorem2.

(* We lost the %N delimiter for ssrnat operations *)
Lemma remark_t2_1 n k (Hank : (a k <= n < a k.+1)%N) :
  (expn n n)%:Q%:C <= n%:Q%:C * exp_quo n%:Q (n * (a k.+1).-2) ((a k.+1).-1).
Proof.
have n_ge1 : (1 <= n)%N by apply: leq_trans (a_pos k) _; lia.
rewrite -{3}[n]expn1 !exp_quo_nat_nat -exp_quo_plus ?ler0n // mul1n muln1.
rewrite exp_quo_lessn ?ler1n //; nia.
Qed.

Lemma remark_t2_2 k1:
  \prod_(i < k1) exp_quo (a i)%:Q (a i).-1 (a i) =
  (\prod_(i < k1) (a i)%:~R) / w_seq k1.
Proof.
rewrite -prodfV -big_split /=; apply: eq_bigr => i _.
by rewrite /a' /exp_quo -subn1 expfB ?a_gt1 // rootCK ?a_pos ?CratrE.
Qed.

End PreliminaryRemarksTheorem2.

Theorem t2 n k (Hank : (a k <= n < (a k.+1))%N) :
  (C n k.+1)%:Q%:C < exp_quo (10%:Q * n%:Q) (2*k.+1 - 1) 2 * (w%:C ^+ n.+1).
Proof.
have n_gt0 : (0 < n)%N.
  by case/andP: Hank => + _; apply/leq_trans/a_pos.
have lt0nC : 0 < n%:Q%:C.
  by rewrite ltr0q ltr0n.
have le0nR : 0 <= n%:Q.
  by rewrite ler0n.
have H10_ge1 : 1 <= (10 * n)%N%:Q.
  by rewrite ler1n muln_gt0.
set cn := (C _ _)%:Q%:C.
set t10n_to := exp_quo (10 * n)%N%:Q.
have wq_ge0 m : 0 <= w%:C ^+ m by rewrite exprn_ge0 // ler0q.
suff step1 : cn < t10n_to (2 * k.+1 - 1)%N 2%N * w%:C ^+ n * w_seq k.+1.
  apply: lt_le_trans step1 _; rewrite -intrM exprSr mulrA.
  by apply/ler_wpmul2l/w_upper_bounded/mulr_ge0/wq_ge0/exp_quo_ge0/ler0n.
rewrite -mulrA; set tw := (X in _ < _ * X).
have tw_pos : 0 <= tw by apply: mulr_ge0.
have tenn_to_pos : 0 <= ((10 * n)%N%:Q ^+ k)%:C.
  by rewrite ler0q exprn_ge0 ?ler0n.
suff step2 : cn < ((10 * n)%N%:Q ^+ k)%:C * t10n_to 1%N (a k.+1).-1 * tw.
  apply: lt_le_trans step2 _; rewrite exp_quo_r_nat.
  have ->: t10n_to (2 * k.+1 - 1)%N 2%N = t10n_to k 1%N * t10n_to 1%N 2%N.
    rewrite -exp_quo_plus ?ler0n //; apply: exp_quo_equiv; ring_lia.
  apply/ler_wpmul2r/ler_wpmul2l/exp_quo_lessn => //; last by rewrite !mul1n.
  by rewrite exp_quo_ge0 // ler0n.
have ->: tw = w%:C ^+ n * n%:Q%:C * (w_seq k.+1 / n%:Q%:C).
  by rewrite mulrACA divff ?lt0r_neq0 // mulr1.
have Helper0 : 0 < \prod_(i < k.+1) (a i)%:~R :> algC by rewrite prodr_gt0.
have Helper1 : 0 < \prod_(i < k.+1) a' i by rewrite prodr_gt0.
have step3 : w_seq k.+1 / n%:Q%:C >=
             (\prod_(i < k.+1) exp_quo (a i)%:Q (a i).-1 (a i))^-1.
  rewrite remark_t2_2 /w_seq invfM // invrK mulrC.
  rewrite ler_pdivr_mulr // -mulrA ler_pmulr // mulrC ler_pdivl_mulr // mul1r.
  case/andP: Hank => _; rewrite a_rec addn1 ltnS big_mkord => H.
  by rewrite -prodMz 2!CratrE ler_nat.
have ler0_10npow : 0 <= ((10 * n)%N%:Q ^+ k)%:C * t10n_to 1%N (a k.+1).-1.
  by rewrite mulr_ge0 ?exp_quo_ge0 ?ler0n.
have t_ge0_0 : 0 <= \prod_(i < k.+1) exp_quo (a i)%:Q (a i).-1 (a i).
  by rewrite prodr_ge0 // => i _; rewrite exp_quo_ge0 // ler0n.
have t_ge0_1 : 0 < exp_quo n%:Q (n * (a k.+1).-2) (a k.+1).-1.
  by rewrite exp_quo_gt0 // ltr0n.
have t_ge0_2 : 0 <= (n ^ n)%N%:Q%:C.
  by rewrite ler0q ler0n.
have t_ge0_3 : 0 <= w_seq k.+1 ^+ n.
  by rewrite exprn_ge0.
have t_ge0_4 : 0 <=
   w_seq k.+1 ^+ n *
   ((n ^ n)%N%:Q%:C / exp_quo n%:Q (n * (a k.+1).-2) (a k.+1).-1).
  by apply/mulr_ge0/divr_ge0/exp_quo_ge0.
suff step4 : cn < ((10 * n)%N%:Q ^+ k)%:C * t10n_to 1%N (a k.+1).-1 *
   ((w_seq k.+1) ^+ n *
    ((n ^ n)%N%:Q%:C / exp_quo n%:Q (n * (a k.+1).-2)%N ((a k.+1).-1)) /
    (\prod_(i < k.+1) exp_quo (a i)%:Q (a i).-1 (a i))).
  apply: lt_le_trans step4 _; apply/ler_wpmul2l/ler_pmul/step3/ler_pmul => //.
  - by rewrite invr_ge0.
  - by rewrite divr_ge0 // ltW.
  - by apply/ler_expn2r/w_upper_bounded; rewrite nnegrE // ler0q.
  - by rewrite ler_pdivr_mulr //; exact: remark_t2_1.
congr (_ < _): (l10 (proj1 (andP Hank))).
have -> : forall k1, exp_quo n%:Q (n * (a k1.+1).-2) (a k1.+1).-1
                     = \prod_(i < k1.+1) exp_quo n%:Q n (a i).
  elim=> [|k1 HIk1]; first by rewrite big_ord_recr big_ord0 /= mul1r muln1.
  rewrite big_ord_recr /= -HIk1 -exp_quo_plus //; apply: exp_quo_equiv => //=.
  - by rewrite muln_gt0 /= muln_gt0; apply/andP.
  - by rewrite muln_gt0 andbT muln_gt0; apply/andP.
  lia.
rewrite /w_seq /t10n_to rmorphX -subn1 -prod_is_exp_sum.
rewrite -3!mulrA ![_ * (_%:C * _)]mulrCA; congr (_ * _).
rewrite -prodrXl -!prodfV -!big_split /=; apply: eq_bigr => i _.
rewrite -exprM mul1n [_^-1 / _ in RHS]mulrC [RHS]mulrA [RHS]mulrACA.
rewrite -!exp_quoV ?divr_ge0 // -intrM -!exp_quoMl ?ler0n //.
by rewrite invfM invrK [_ * (a i)%:~R]mulrC.
Qed.


Theorem t2_rat n k (Hank : (a k <= n < (a k.+1))%N) :
  (C n k.+1)%:Q < (10%:Q * n%:Q) ^ k.+1 * (w ^+ n.+1).
Proof.
suff : (C n k.+1)%:Q%:C < exp_quo (10%:Q * n%:Q) (2 * k.+1) 2 * w%:C ^+ n.+1.
  by rewrite /exp_quo exprM sqrtCK -!rmorphX /= -rmorphM /= ltr_rat.
apply: lt_le_trans (t2 Hank) _; apply: ler_wpmul2r.
  by rewrite exprn_ge0 ?ler0q.
case: n {Hank} => [| n]; first by rewrite mulr0 !exp_quo_0 /= mulnC muln2.
by apply: exp_quo_lessn=> //; [ring_lia | lia].
Qed.

Lemma better_k_bound n k (Hank : (a k <= n < a k.+1)%N) :
  (k <= trunc_log 2 (trunc_log 2 n) + 2)%N.
Proof.
case: k Hank => [| k] //; case: k => [| k Hank]; last exact: k_bound.
by rewrite addn2.
Qed.

Theorem t3_nat : exists K : nat,
    (0 < K)%N /\ forall n : nat, (iter_lcmn n <= K * 3 ^ n)%N.
Proof.
pose cond n k := (a k <= n < a k.+1)%N.
suff [K [Kpos KP]] : exists K : nat,
    (0 < K)%N /\ (forall n k, cond n k -> C n k.+1 <= K * 3 ^ n)%N.
  exists K; split => // -[| n]; first by rewrite expn0 muln1 iter_lcmn0.
  case: n => [| n]; first by rewrite iter_lcmn1 muln_gt0 Kpos.
  by apply/leq_trans/KP/n_between_a => //; apply/lcm_leq_Cnk.
suff [K [Kpos KP]] : exists K : rat,
    (0 < K) /\ forall n k, cond n k -> (C n k.+1)%:R <= K * 3%:R ^ n.
  move: (floorQ K) (floorQ_ge0 (ltW Kpos)) (floorQ_spec K).
  case=> // k _ /andP [_ leKSn]; exists k.+1; split=> // n m {}/KP KP.
  suff: (C n m.+1)%:R <= (k%:Q + 1) * 3%:R ^ n.
    by rewrite -[_ + 1%:R]natrD -[_ ^ n]natrX -natrM ler_nat addn1.
  exact/le_trans/ler_wpmul2r/ltW/leKSn/exprz_ge0.
move mE: 10%:Q => m.
have lt0m : 0 < m by rewrite -mE.
have le0m : 0 <= m by exact: ltW.
have lt1m : 1 < m by rewrite -mE.
have le1m : 1 <= m by exact: ltW.
move epsE: (w / 3%:R) => eps.
have lt0eps1 : 0 < eps < 1.
  by rewrite -epsE ltr_pdivl_mulr // mul0r ltr_pdivr_mulr // mul1r w_lt3 w_gt0.
pose u n k eps : rat := (m * n%:R) ^ k.+1 * eps ^ n.+1.
suff hloglog : exists (K : rat), (0 < K) /\ (forall n k, cond n k -> u n k eps < K).
  have [K [lt0K KP]] := hloglog.
  exists (K * 3%:Q); split; first exact: mulr_gt0.
  move=> n k hcond.
  apply: le_trans (ltW (t2_rat hcond)) _; rewrite -mulrA -exprSz.
  rewrite -ler_pdivr_mulr; last exact: exprz_gt0.
  by rewrite -mulrA -expr_div_n mE epsE; apply/ltW/KP.
have [lt0eps  lteps1] := andP lt0eps1.
pose loglog n := trunc_log 2 (trunc_log 2 n).
pose v n : rat := (m * n%:R) ^ (loglog n).+3 * eps ^ n.+1.
have le0v n : 0 <= v n.
  by rewrite /v pmulr_lge0 ?exprz_gt0 // exprz_ge0 // mulr_ge0 // ler0n.
suff {u} [K [Kpos KP]] : exists K : rat, 0 < K /\ forall n, v n < K.
  exists K; split => // n k /better_k_bound hkn; apply: le_lt_trans (KP n).
  rewrite /u /v ler_pmul2r; last exact: exprz_gt0.
  case: n hkn => [| n] hkn; first by rewrite mulr0 !exp0rz.
  apply: exp_incr_expp; first by apply: mulr_ege1=> //; rewrite ler1n.
  by rewrite ltnS -addn2.
have h1 n : ((trunc_log 2 n).+1 <= 2 ^ (loglog n).+1)%N by exact: trunc_log_ltn.
have {}h1 n : (n < 2 ^ 2 ^ (loglog n).+1)%N.
  have h : (n < 2 ^ (trunc_log 2 n).+1)%N by exact: trunc_log_ltn.
  have {}h : (2 ^ (trunc_log 2 n).+1 <= 2 ^ 2 ^ (loglog n).+1)%N by rewrite leq_exp2l.
  exact/leq_trans/h/trunc_log_ltn.
have h2 n : (1 < n)%N -> (2 ^ 2 ^ loglog n <= n)%N.
  move=> lt1n.
  have h: (2 ^ trunc_log 2 n <= n)%N by apply/trunc_logP/ltnW.
  apply: leq_trans h; rewrite leq_exp2l; last by [].
  exact/trunc_logP/trunc_log_max.
pose y n := (2 ^ 2 ^ (loglog n).+1)%N; pose x n := (2 ^ 2 ^ loglog n)%N.
pose t n := (m * (y n)%:R) ^ (loglog n).+3 * eps ^ (x n).+1.
have le0y n : 0 <= (y n)%:R :> rat by rewrite ler0n.
suff {v le0v} [K [Kpos KP]] : exists K : rat, 0 < K /\ forall n, t n < K.
  pose KK := K + v 0%N + v 1%N.
  have ltKKK : K <= KK by rewrite /KK -addrA ler_addl addr_ge0.
  have ltvKK n : (n <= 1)%N -> v n < KK.
    rewrite leq_eqVlt ltnS leqn0 /KK => /orP [] /eqP ->.
    - by rewrite cpr_add ltr_spaddl.
    - by rewrite addrAC  cpr_add ltr_spaddl.
  exists KK; split => [|n]; first exact: lt_le_trans ltKKK.
  have [le1n | lt1n] := leqP n 1; first exact: ltvKK.
  apply/lt_le_trans/ltKKK/le_lt_trans/(KP n); rewrite /v /t.
  (* use case for posreal-style automation... *)
  apply/ler_pmul/exp_incr_expn => //.
  - exact/exprz_ge0/mulr_ge0/ler0n.
  - exact/exprz_ge0/ltW.
  - apply: ler_expn2r; last first.
    + by apply: ler_wpmul2l; rewrite // ler_nat ltnW // h1.
    + by rewrite rpredM // rpred_nat.
    + by rewrite rpredM // rpred_nat.
  - by rewrite ltnS h2.
pose u n := (m * (x n)%:R) ^+ (2 * (loglog n).+3) * eps ^ x n.
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
have {}h2 n : (1 < n)%N -> (x n <= n)%N by apply: h2.
pose alpha n := (2 ^ 2 ^ n)%N.
have le0alpha n : 0 <= (alpha n)%:R :> rat by rewrite ler0n.
have lt_0_alpha n : (0 < alpha n)%N by rewrite /alpha expn_gt0.
pose t n := (m * (alpha n)%:R) ^ (2 * n.+3)%:Z * eps ^ alpha n.
have lt_0_t n : 0 < t n.
  by apply/mulr_gt0/exprz_gt0/lt0eps/exprz_gt0/mulr_gt0; rewrite ?ltr0n.
have le_0_t n : 0 <= t n by exact: ltW.
suff {x h1 h2 u} [K [Kpos KP]] : exists K : rat, 0 < K /\ forall n, t n < K.
  by exists K; split => // n; apply: le_lt_trans (KP (loglog n)).
pose l n := (alpha n)%:R ^ 4 * eps ^ ((alpha n)%:Z ^ 2 - 2%:Z * (alpha n)%:Z).
have alphaS n : (alpha n.+1 = alpha n ^ 2)%N.
  by rewrite /alpha expnS mulnC expnM.
have le_0_alpham2 k : 0 <= (alpha k)%:Z - 2%:Z.
  rewrite /alpha; apply: (@le_trans _ _ ((2 ^ 2 ^ 0)%:Z - 2%:Z)) => //.
  by apply: ler_sub=> //; rewrite lez_nat leq_exp2l // leq_exp2l.
have maj_t n : t n.+1 <= t n ^ 2 * l n.
  rewrite /t 2!expfzMl !exprz_exp expfzMl -2!mulrA -[_ * _ * l n]mulrA.
  apply: ler_pmul; first exact: exprz_ge0. (* missing posreal... *)
  - apply: mulr_ge0; apply: exprz_ge0 => //; exact: ltW.
  - rewrite ler_weexpn2l //; lia.
  rewrite /l mulrCA 2!mulrA -exprzD_nat -mulrA -expfzDr; last exact: lt0r_neq0.
  apply: ler_pmul; first exact: exprz_ge0. (* missing posreal... *)
  - apply: exprz_ge0; exact: ltW.
  - rewrite alphaS natrX exprnP exprz_exp ler_weexpn2l //; last lia.
    by rewrite ler1n expn_gt0.
  - by rewrite addrCA mulrC addrN addr0 alphaS.
have le_0_l n : 0 <= l n. 
  rewrite /l; apply: mulr_ge0; first by apply/exprz_ge0/ler0n.  
  by apply/exprz_ge0/ltW.
pose eps1 := rat_of_Z 5949909309448377. 
pose eps2 := rat_of_Z (6 * 10 ^ 15).
have lt0eps2 : 0 < eps2 by exact: rat_of_Z_Zpos. 
have eps2_val : eps2 = 3%:R * rat_of_Z (2 * 10 ^ 15).
  by rewrite /eps2; ring.
have epsF : eps = eps1 / eps2.
  by rewrite -epsE eps2_val invfM [RHS]mulrA [RHS]mulrAC w_val.
have a3 : alpha 3%N = expn 2 8 by [].
have lt_l3_1 : l 3%N <= 1.
  have -> : l 3%N = (2%:R * eps ^ (2%:R ^ 3 * ((alpha 3%N)%:R - 2%:R))) ^ (2 ^ 5)%N%:R.
    rewrite /l a3 [RHS]expfzMl -!natz !natrX !natz !exprnP !exprz_exp.
    by congr (_ ^ _ * eps ^ _).
  rewrite expr_le1 //; last exact/mulr_ge0/exprz_ge0/ltW.
  suff: 2%:R * eps ^ 90 <= 1.
    by apply: le_trans; rewrite ler_pmul2l ?ler_piexpz2l.
  rewrite epsF expfzMl -expfV mulrA ler_pdivr_mulr; last exact: exprz_gt0.
  rewrite mul1r -subr_ge0 -!rat_of_Z_pow mulr_natl -rmorphMn -rmorphB.
  vm_compute; exact: rat_of_Z_ZposW.
rewrite [l]lock in lt_l3_1.
have lt_t4_1 : t 4%N < 1.
  rewrite {l le_0_l lt_l3_1 maj_t loglog a3}.
  pose a4 := locked alpha 4%N.
  have lt0a4 : (0 < a4)%N by rewrite /a4 -lock.
  have -> : t 4%N = (m * a4%:R) ^ 14 * eps ^ alpha 4%N by rewrite /t /a4 -lock.
  suff [M hM hm]: exists2 M, (M * 14 <= alpha 4)%N & (m * a4%:R) * eps ^ M < 1.
    have {hm} : (m * a4%:R) ^14 * eps ^ (M * 14)%N < 1.
      rewrite PoszM -exprz_exp -expfzMl; apply: exprn_ilt1=> //.
      rewrite -mulrA pmulr_rge0 // pmulr_rge0 ?ltr0n //; apply: exprz_ge0; exact: ltW.
    apply: le_lt_trans. rewrite ler_pmul2l; first by rewrite ler_piexpz2l.
    by apply: exprz_gt0; rewrite pmulr_rgt0 // ltr0n.
  pose e := rat_of_Z 992 / rat_of_Z (10 ^ 3).
  have ltepse : eps < e.
    rewrite epsF ltr_pdivr_mulr // /e mulrAC ltr_pdivl_mulr; last  exact: rat_of_Z_Zpos.
    have -> : eps2 = rat_of_Z (6 * 10 ^ 12) * rat_of_Z (10 ^ 3).
      by rewrite /eps2; ring.
    rewrite mulrA ltr_pmul2r ?rat_of_Z_Zpos //.
    rewrite -subr_gt0 /eps1 -rmorphM -rmorphB.
    exact: rat_of_Z_Zpos. (* long *)
  suff [M le14M]: exists2 M, (M * 14 <= alpha 4)%N & (m * a4%:R) * (e ^ M) < 1.
    move=> hm; exists M => //; apply: le_lt_trans hm. rewrite ler_pmul2l; last first.
      by rewrite pmulr_rgt0 // ltr0n.
    by apply: ler_expn2r; apply: ltW; rewrite // divr_gt0 // rat_of_Z_Zpos.
  suff [M le14M hm]: exists2 M, (M * 14 <= alpha 4)%N &
      0 < rat_of_Z (10 ^ 3) ^ M -  (m * a4%:R) * rat_of_Z 992 ^ M.
    exists M => //.
    rewrite /e  expfzMl -expfV mulrA ltr_pdivr_mulr; last by rewrite exprz_gt0 // rat_of_Z_Zpos.
    by rewrite mul1r -subr_gt0.
  exists 2000%N; first by rewrite /alpha -subn_eq0. (* FIXME : compute in Z. *)
  rewrite -mE -!rat_of_Z_pow.
  rewrite pmulrn -intrM mulrzl -rmorphMz -rmorphB -mulrzl intrM.
  rewrite /a4 -lock /alpha.
  vm_compute; exact: rat_of_Z_Zpos. (* long *)
rewrite [t]lock in lt_t4_1.
have lt_ln_1 (n : nat) : (3 <= n)%N -> l n <= 1.
  elim: n => [// | n ihn].
  rewrite leq_eqVlt => /predU1P [<- | {}/ihn ihn]; first by rewrite [l]lock. (* unlock does not work... *)
  suff h : l n.+1 <= (l n) ^ 2 by apply: le_trans h _; apply: mulr_ile1.
  rewrite /l expfzMl exprz_exp; apply: ler_pmul.
  - exact/exprz_ge0/ler0n.
  - exact/exprz_ge0/ltW.
  - by rewrite alphaS natrX exprnP exprz_exp.
  rewrite exprz_exp ler_piexpz2l //.
  - rewrite alphaS -subr_ge0; set a := alpha _; set x := (X in 0 <= X).
    have {x} -> : x = a%:Z ^+ 2 ^+ 2 - (2%:Z * a%:Z) ^+ 2 + 4%:Z * a%:Z.
      by rewrite /x; ring.
    rewrite subr_sqr; apply: addr_ge0; apply: mulr_ge0 => //.
    by rewrite expr2 -mulrBl; apply/mulr_ge0/isT/le_0_alpham2.
  - by rewrite -topredE /= -mulrBl; apply: mulr_ge0; first exact: le_0_alpham2.
  - by rewrite -topredE /= -mulrBl; apply: mulr_ge0; first exact: mulr_ge0.
suff [K [lt0K [N Pn]]] : exists K : rat,  0 < K /\ exists N : nat, (forall n, (N < n)%N -> t n < K).
  (* a bigenough would be nice here *)
  pose KK := (K + \sum_(0 <= j < N.+1) t j).
  have le0sum : 0 <= \sum_(0 <= j < N.+1) t j by apply: sumr_ge0=> n _; exact: ltW.
  have lt0KK : 0 < KK by rewrite /KK; apply: ltr_spaddl.
  have ltKK : K <= KK by rewrite /KK ler_addl.
  have KKmaj j : (j <= N)%N -> t j < KK.
    move=> lej4; rewrite /KK (bigD1_seq j) //=; last by rewrite mem_iota iota_uniq.
    - rewrite addrA addrAC cpr_add; apply: ltr_spaddl=> //; apply: sumr_ge0=> n _; exact: ltW.
    by rewrite mem_index_iota.
  exists KK; split => //; elim=> [| n ihn]; first exact: KKmaj.
  case: (ltnP n.+1 N.+1) => [lenN | ltNn]; first exact: KKmaj.
  by apply: lt_le_trans ltKK; apply: Pn.
exists 1; split => //; exists 3%N; elim=> [| n ihn] //.
rewrite leq_eqVlt => /predU1P [<- | lt3n]; first by rewrite [t]lock.
have {}ihn := ihn lt3n.
apply: le_lt_trans (maj_t _) _; apply: (@le_lt_trans _ _ (t n ^ 2)); last first.
  by apply: mulr_ilt1.
rewrite ger_pmulr; first by apply: lt_ln_1; rewrite ltnS in lt3n; apply: ltn_trans lt3n.
exact: exprz_gt0.
Qed.



Theorem t3 : exists (K : nat),
    (0 < K)%N /\
    forall n, (iter_lcmn n)%:Q <= (K * expn 3 n)%N%:Q.
Proof.
have [K [Kpos Kmaj]] := t3_nat.
by exists K; split => // n; rewrite ler_nat.
Qed.

End Hanson.
