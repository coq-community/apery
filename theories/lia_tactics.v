Require Import ZArith.
Require Import Psatz.

From mathcomp Require Import all_ssreflect all_algebra. 

Require Import shift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Delimit Scope Z_scope with coqZ.

(* Translation of type int into type Z *)
Definition Z_of_int (n : int) : Z := 
match n with
  |Posz k => Z_of_nat k
  |Negz k => Z.opp (Z_of_nat k.+1)
end.

(* Correspondance bewteen comparison relations *)
Lemma Z_of_intP n m : n = m <-> Z_of_int n = Z_of_int m.
Proof. 
split; first by move->.
case: n=> [[|nn]|nn]; case: m => [[|mm]|mm] //=.
- by rewrite !Zpos_P_of_succ_nat; move/Z.succ_inj/inj_eq_rev->.
- case; move/(f_equal Zpos); rewrite !Zpos_P_of_succ_nat.
  by move/Z.succ_inj/inj_eq_rev->.
Qed.

Lemma Z_of_intbP n m : n == m <-> Z_of_int n = Z_of_int m.
Proof. by rewrite <- Z_of_intP; split; move/eqP. Qed.

Lemma Z_of_intbPn n m : n != m <-> Z_of_int n <> Z_of_int m.
Proof. by rewrite <- Z_of_intP; split; move/eqP. Qed.

Lemma Z_ltP (x y : int) : (x < y) <-> (Z.lt (Z_of_int x) (Z_of_int y)).
Proof.
split; case: x=> [[|xx]|xx]; case: y => [[|yy]|y] //.
- move=> h; rewrite /= !Zpos_P_of_succ_nat; apply: Zsucc_lt_compat; apply: inj_lt.
  exact: ssrnat.ltP.
- rewrite /Z_of_int; rewrite !NegzE => h.
  have {h} : (Z_of_nat y.+1 < Z_of_nat xx.+1)%coqZ by apply/inj_lt/ssrnat.ltP.
  by lia.
- by rewrite /= !Zpos_P_of_succ_nat; move/Zsucc_lt_reg/inj_lt_rev/ssrnat.ltP.
- rewrite /Z_of_int !NegzE => h.
- have {h} : (Z_of_nat y.+1 < Z_of_nat xx.+1)%coqZ by lia.
  by move/inj_lt_rev/ssrnat.ltP.
Qed.

Lemma Z_leP (x y : int) : (x <= y) <-> Z.le (Z_of_int x) (Z_of_int y).
Proof.
split.
- rewrite le_eqVlt; case/orP; first by move/eqP->; exact: Z.le_refl.
  move/Z_ltP; exact: Zlt_le_weak.
case/Z_le_lt_eq_dec; first by move/Z_ltP/ltW.
by move/Z_of_intP->.
Qed.

(*Transformation of a constraint (x # y) where (x y : int) and # is a comparison 
relation into the corresponding constraint (Z_of_int x #' Z_of_int y) where #' is
the analogue of # on Z. The transformation is performed on the first such formula
found either in the context or the conclusion of the goal *)
Ltac zify_int_rel :=
 match goal with
  (* Prop equalities *)
  | H : (@eq _ _ _) |- _ => move/Z_of_intP: H => H
  | |- (@eq _ _ _) => rewrite -> Z_of_intP
  | H : context [ @eq _ ?a ?b ] |- _ => rewrite -> (Z_of_intP a b) in H
  | |- context [ @eq _ ?a ?b ] => rewrite -> (Z_of_intP a b)
  (* less than *)
  | H : is_true (@Order.lt _ _ _ _) |- _ => move/Z_ltP: H => H
  | |- is_true (@Order.lt _ _ _ _) => rewrite -> Z_ltP
  | H : context [  is_true (@Order.lt _ _ ?a ?b) ] |- _ => rewrite -> (Z_ltP a b) in H
  | |- context [ is_true (@Order.lt _ _ ?a ?b) ] => rewrite -> (Z_ltP a b)
  (* less or equal *)
  | H : is_true (@Order.le _ _ _ _) |- _ => move/Z_leP: H => H
  | |- is_true (@Order.le _ _ _ _) => rewrite -> Z_leP
  | H : context [  is_true (@Order.le _ _ ?a ?b) ] |- _ => rewrite -> (Z_leP a b) in H
  | |- context [  is_true (@Order.le _ _ ?a ?b) ] => rewrite -> (Z_leP a b)
  (* Boolean equality *)
  |H : is_true (@eq_op _  _ _) |- _ => rewrite -> Z_of_intbP in H
  | |- is_true (@eq_op _  _ _) => rewrite -> Z_of_intbP
  |H : context [ is_true (@eq_op _  _ _)] |- _ => rewrite -> Z_of_intbP in H
  | |- context [ is_true (@eq_op _  _ _)] => rewrite -> Z_of_intbP
  (* Negated boolean equality *)
  |H : is_true (negb (@eq_op _  _ _)) |- _ => rewrite -> Z_of_intbPn in H
  | |- is_true (negb (@eq_op _  _ _)) => rewrite -> Z_of_intbPn
  |H : context [ is_true (negb (@eq_op _  _ _))] |- _ => rewrite -> Z_of_intbPn in H
  | |- context [ is_true (negb (@eq_op _  _ _))] => rewrite -> Z_of_intbPn
 end.

(* Distribution of Z_of_int over arithmetic operations *)
Lemma Z_of_intmorphD  : {morph Z_of_int : x y  /  x + y >-> (Zplus x y) }.
Proof.
have aux (n m : nat) : 
  Z_of_int (Posz n.+1 + Negz m) = (Z_of_int n.+1 + Z_of_int (Negz m))%coqZ.
  rewrite {2 3}/Z_of_int NegzE; case: (ltngtP m n)=> hmn.
  + rewrite subzn; last exact: ltn_trans hmn _.
    rewrite subSn // /Z_of_int -subSn // inj_minus1 //; apply/ssrnat.leP.
    exact: ltn_trans hmn _.
  + rewrite -[_ - _]opprK opprB subzn; last exact: ltn_trans hmn _.
    rewrite subSn // -NegzE /Z_of_int -subSn // inj_minus1; first by lia.
    apply/ssrnat.leP; exact: ltn_trans hmn _.
  + by rewrite hmn subrr Zplus_opp_r.
move=> x y /=; case: x=> [[|xx]|xx]; case: y => [[|yy]|y] //.
- by rewrite /= subn0.
- by rewrite addr0 Zplus_0_r.
- by rewrite -PoszD addnS /Z_of_int -inj_plus -addnS.
- by rewrite addr0 Zplus_0_r.
- by rewrite addrC aux Zplus_comm.
- rewrite {2 3}/Z_of_int !NegzE -opprD -PoszD addnS -NegzE /Z_of_int -addnS.
  by rewrite inj_plus Zopp_plus_distr.
Qed.

Lemma Z_of_intmorphM  : {morph Z_of_int : x y  / x * y  >-> (Zmult x y) }.
have aux (n m : nat) :  
  Z_of_int (Posz n.+1 * Negz m) = (Z_of_int n.+1 * Z_of_int (Negz m))%coqZ.
  rewrite {2 3}/Z_of_int NegzE mulrN -PoszM mulnS addSn -NegzE /Z_of_int -addSn.
  by rewrite -mulnS inj_mult; lia.
move=> x y /=; case: x=> [[|xx]|xx]; case: y => [[|yy]|y] //.
- by rewrite mulr0 Zmult_0_r.
- by rewrite -PoszM /Z_of_int inj_mult.
- by rewrite mulrC aux Zmult_comm.
- rewrite ![in LHS]NegzE mulrN mulNr opprK -PoszM /Z_of_int inj_mult; lia.
Qed.

Lemma Z_of_intmorphN  : {morph Z_of_int : x / - x >-> Z.opp x}.
Proof. by case=> [] [|xx]. Qed.

Lemma Z_of_int_shift z n : 
  Z_of_int (int.shift n z) = Zplus (Z_of_int z) (Z_of_nat n).
Proof. by rewrite int.shift2Z Z_of_intmorphD. Qed.

Lemma Z_of_int_shift1 z : 
  Z_of_int (int.shift1 z) = Zplus (Z_of_int z) 1.
Proof. by rewrite int.shift2Z Z_of_intmorphD. Qed.

(*Pushing Z_of_int at the leaves of expressions.The transformation is *)
(*performed on the first such formula found either in the context or *)
(*the conclusion of the goal *)
(* We (boldly?) assume here that all operations are ring ones *)
Ltac zify_int_op :=
 match goal with
  (* add -> Zplus *)
  | H : context [ Z_of_int (@GRing.add _ _ _) ] |- _ => rewrite Z_of_intmorphD in H
  | |- context [ Z_of_int (@GRing.add _ _ _) ] => rewrite Z_of_intmorphD
  (* opp -> Z.opp *)
  | H : context [ Z_of_int (@GRing.opp _ _) ] |- _ => rewrite Z_of_intmorphN in H
  | |- context [ Z_of_int (@GRing.opp _  _) ] => rewrite Z_of_intmorphN
  (* mul -> Zmult *)
  | H : context [ Z_of_int (@GRing.mul _ _ _) ] |- _ => rewrite Z_of_intmorphM in H
  | |- context [ Z_of_int (@GRing.mul _ _ _) ] => rewrite Z_of_intmorphM
  (* (* O -> Z0 *) *)
  | H : context [ Z_of_int (GRing.zero _) ] |- _ => rewrite [Z_of_int O]/= in H
  | |- context [ Z_of_int (GRing.zero _) ] => rewrite [Z_of_int O]/=
  (* (* 1 -> 1 *) *)
  | H : context [ Z_of_int (GRing.one _) ] |- _ => rewrite [Z_of_int 1]/= in H
  | |- context [ Z_of_int (GRing.one _) ] => rewrite [Z_of_int 1]/=
  (* (* n -> n *) *)
  | H : context [ Z_of_int _ ] |- _ => rewrite [Z_of_int (S _)]/= in H
  | |- context [ Z_of_int _ ] => rewrite [Z_of_int (S _)]/=
  | H : context [ Z_of_nat _ ] |- _ => rewrite [Z_of_nat 0]/= [Z_of_nat (S _)]/= in H
  | |- context [ Z_of_nat _ ] => rewrite [Z_of_nat 0]/= [Z_of_nat (S _)]/=
  (* shifts *)
  | H : context [int.shift _ _] |- _ => rewrite Z_of_int_shift in H
  | H : context [int.shift1 _] |- _ => rewrite Z_of_int_shift1 in H
  | |- context [int.shift _ _] => rewrite Z_of_int_shift
  | |- context [int.shift1 _] => rewrite Z_of_int_shift1
 end.

(* Preparing a goal to be solved by lia by translating every formula *)
(* in the context or the conclusion which expresses a constraint on *)
(* some int into the analogue on Z *)
Ltac zify_int :=
  repeat progress zify_int_rel;
  repeat progress zify_int_op.

(* Preprocessing + lia *)
Ltac intlia := zify_int; lia.

(* Below starts the code of goal_to_lia, to be cleaned as well *)

Lemma eqr_int_prop (x y : int) :
 (x%:~R = y%:~R :> rat) <-> x = y.
Proof.
split; last by move ->.
by move/eqP; rewrite eqr_int; move/eqP.
Qed.


Ltac rat_to_ring_lia :=
  rewrite -?[0%Q]/((Posz 0)%:~R : rat) -?[1%Q]/((Posz 1)%:~R : rat)
          -?[(_ - _)%Q]/(_ - _ : rat)%R -?[(_ / _)%Q]/(_ / _ : rat)%R
          -?[(_ + _)%Q]/(_ + _ : rat)%R -?[(_ * _)%Q]/(_ * _ : rat)%R
          -?[(- _)%Q]/(- _ : rat)%R -?[(_ ^-1)%Q]/(_ ^-1 : rat)%R /=.

Ltac rat_to_ring_hyp hyp :=
  rewrite -?[0%Q]/((Posz 0)%:~R : rat) -?[1%Q]/((Posz 1)%:~R : rat)
          -?[(_ - _)%Q]/(_ - _ : rat)%R -?[(_ / _)%Q]/(_ / _ : rat)%R
          -?[(_ + _)%Q]/(_ + _ : rat)%R -?[(_ * _)%Q]/(_ * _ : rat)%R
          -?[(- _)%Q]/(- _ : rat)%R -?[(_ ^-1)%Q]/(_ ^-1 : rat)%R /= in hyp.

Ltac propify_bool_connectives :=
rewrite ?(negb_and, negb_or);
repeat (match goal with
 | H : context [ is_true (andb _ _) ] |- _ => rewrite -(rwP andP) in H
 | |-  context [ is_true (andb _ _) ]      => rewrite -(rwP andP)
 | H : context [ is_true (orb _ _) ] |- _ => rewrite -(rwP orP) in H
 | |-  context [ is_true (orb _ _) ]      => rewrite -(rwP orP) end);
rewrite ?(=^~ ltNge, =^~ leNgt).

Ltac goal_to_lia :=
propify_bool_connectives;
rat_to_ring_lia;
rewrite ?NegzE;
(* unpropagate morZ_of_intsms to get, where that is pertinent,*)
(* propositions of the form _%:~R =/<=/< _%:~R *)
rewrite -?(rmorphD,rmorphN, rmorphB,rmorphM);
(* get rid of the cast %:~R around various compare operations *)
rewrite ?(eqr_int,ler_int,ltr_int,eqr_int_prop); (* TODO: add nats here *)
(* put Z_of_int around the sides of the operation =,<=,or < (on ints)  *)
try (rewrite -> !Z_of_intbPn);
try (rewrite -> !Z_of_intbP);
try (rewrite -> !Z_ltP);
try (rewrite -> !Z_leP);
try (rewrite -> !Z_of_intP); (* TODO: add nats here *)
(* just in case there were some trapped nats inside the goal *)
rewrite ?(PoszD,PoszM);
(* distribute Z_of_int to the leaves of the arithmetic expressions *)
rewrite ?(Z_of_intmorphN, Z_of_intmorphM, Z_of_intmorphD) 
?[Z_of_int 1]/= ?[Z_of_int 0]/= ?[Z_of_int (S _)]/=;
(* somehow we obtain (is_true true) somewhere and lia dislikes it *)
repeat (rewrite [true](erefl : true = (0 < (1 : int))));
repeat (rewrite [false](erefl : false = (0 < (0 : int)))).
