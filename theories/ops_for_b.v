Load "include/ops_header.v".

Require annotated_recs_v.

Module v.
Include annotated_recs_v.
End v.

Section AnnOfB.

Variable v : int -> int -> rat.
Variable v_ann : v.Ann v.
Let v_Sn2 := v.Sn2_ v_ann.
Let v_SnSk := v.SnSk_ v_ann.
Let v_Sk2 := v.Sk2_ v_ann.


Theorem P_eq_Delta_Q : v.CT v.
Proof.
rewrite /v.CT => n k; rewrite /v.not_D; andb_to_and => notD.
rewrite /v.P_horner /v.P_seq /punk.horner_seqop /= /v.Q_flat.
do 5! (rewrite v_Sn2;
            last by rewrite /v.precond.Sn2 ?int.shift2Z; intlia).
rewrite v_SnSk;
  last by rewrite /v.precond.SnSk ?int.shift2Z; intlia.
rewrite v_Sk2; last by rewrite /v.precond.Sk2 ?int.shift2Z; intlia.
(* Sanity check: at this point, we have a normal form wrt the Gröbner basis. *)
set v1 := v _ _; set v2 := v _ _; set v3 := v _ _.  (* set v4 := v _ _. *)
(* This unfolding takes a dozen seconds if the Q_cf<i> are unfolded first: *)
(* they are the largest objects in this formalization. *)
rewrite
  /v.P_cf0 /v.P_cf1 /v.P_cf2 /v.P_cf3 /v.P_cf4
  /v.Sk2_cf0_0 /v.Sk2_cf0_1 /v.Sn2_cf0_0 /v.Sn2_cf1_0 /v.Sn2_cf0_1
  /v.SnSk_cf0_0 /v.SnSk_cf1_0 /v.SnSk_cf0_1
  /v.Q_cf0_0 /v.Q_cf1_0 /v.Q_cf0_1
.
rewrite !int.shift2R.
(* This takes over 250 seconds. *)
rat_field.
by goal_to_lia; intlia.
Qed.


Let b (n : int) : rat := \sum_(0 <= k < n + 1 :> int) v n k.

Theorem recAperyB (n : int) : n >= (2 : int) -> v.P_horner b n = 0.
Proof using v v_ann v_Sn2 v_SnSk v_Sk2 b.
move=> nge2.
rewrite /v.P_horner.
rewrite (punk.sound_telescoping P_eq_Delta_Q) //;
  last exact: (addr_ge0 (le_trans _ nge2) _).
set onD := (X in _ + X + _).
set remP := (X in _ + _ + X).
set F := BIG_F in onD *.
(* Terms on onD are just the three following specializations. *)
have {onD} -> : onD = F 0 + F (n - 1) + F n.
  rewrite /onD /v.not_D.
  rewrite /punk.horner_seqop.
  rewrite /punk.horner_seqop_rec /=.
  rewrite big_mkcond /= big_int_recl /=; last by intlia.
  rewrite ifT; last by goal_to_lia; intlia.
  have hn : n = (n - 1 - 1) + 1 + 1 by intlia.
  rewrite {1}[in LHS]hn.
  rewrite big_int_recr /=; last by move: nge2; clear; intlia.
  rewrite ifT; last by move: nge2; clear; goal_to_lia; intlia.
  rewrite big_int_recr /=; last by move: nge2; clear; intlia.
  rewrite ifT; last by move: nge2; clear; goal_to_lia; intlia.
  rewrite -hn [n - 1 - 1 + 1]addrNK -big_mkcond big_int_cond big_pred0
      => [ | i].
    by rewrite add0r addrA.
  by apply: negPf; move: nge2; clear; goal_to_lia; intlia.
(* Now we chase pathological denominators that may occur in values of F
   and "telQ". *)
rewrite {}/F.
rewrite add0r [n - 1 + 1]addrNK.
(* In fact, simplifying natural compensations is enough. *)
(* We use some abbreviations to ease the description of the simplified form. *)
set pv_0_S1 := punk.horner_seqop _ _ _.
set pv_S0_S1 := punk.horner_seqop _ _ _.
set pv_S1_S1 := punk.horner_seqop _ _ _.
set q_S1_S2 := v.Q_flat _ _ _.
set q_S1_0 := v.Q_flat _ _ _.
set q_S1_1 := v.Q_flat _ _ _.
set q_S1_S1 := v.Q_flat _ _ _.
set q_S1_S0 := v.Q_flat _ _ _.
Fail set q := v.Q_flat _ _ _.
set L := (X in (X + _ = _)).
have -> : L = pv_0_S1 - q_S1_1 + pv_S0_S1 + q_S1_S0 + pv_S1_S1.
  rewrite /L; rat_field.
clear L q_S1_S2 q_S1_0 q_S1_S1.
(* No more pathological denominators in the remaining terms. *)
(* We can observe two groups of terms: one right and above (n, 0) *)
(* produced by pv_0_S1 and q_S1_1, and one right and above (n -1, n -1), *)
(* produced by the other terms. We normalize them independently, since *)
(* they cannot interact to give the zero answer. *)
set around_n_0 := pv_0_S1 - q_S1_1.
have -> : around_n_0 = 0.
  rewrite {}/around_n_0.
  clear pv_S0_S1 pv_S1_S1 q_S1_S0 remP.
  rewrite {}/pv_0_S1 {}/q_S1_1.
  (* Unrolling the definition of P *)
  rewrite /punk.horner_seqop /punk.horner_seqop_rec /=.
  (* Unrolling the definition of Q *)
  rewrite /v.Q_flat.
  (* Just to ease reading, a few abbreviations *)
  set c10 := v (int.shift 1 n) 0.
  set c20 := v (int.shift 2 n) 0.
  set c30 := v (int.shift 3 n) 0.
  set c40 := v (int.shift 4 n) 0.
  set c11 := v (int.shift 1 n) (int.shift 1 0).
  set c02 := v n (int.shift 2 0).
  set c01 := v n 1.
  set c00 := v n 0.
  Fail set c := v _ _.
  (* This one will be produced by the normalization *)
  pose c21 := v (int.shift 2 n) (int.shift 1 0).
  rewrite [c40]v_Sn2; last first.
    rewrite /v.precond.Sn2; goal_to_lia; intlia.
  rewrite {c40} -/c30 -/c20 -/c21.
  rewrite [c30]v_Sn2; last first.
    rewrite /v.precond.Sn2; goal_to_lia; intlia.
  rewrite {c30} -/c20 -/c11 -/c10.
  rewrite [c21]v_SnSk; last first.
   rewrite /v.precond.SnSk; goal_to_lia; intlia.
  rewrite {c21} -/c11 -/c20 -/c10.
  rewrite [c20]v_Sn2; last first.
    by rewrite /v.precond.Sn2; goal_to_lia; intlia.
  rewrite {c20} -/c00 -/c10 -/c01.
  rewrite [c02]v_Sk2; last first.
    rewrite /v.precond.Sk2; goal_to_lia; intlia.
  rewrite {c02} -/c00 -/c01.
  rewrite [c11]v_SnSk; last first.
   rewrite /v.precond.SnSk; goal_to_lia; intlia.
  rewrite {c11} -/c00 -/c01 -/c10.
 (* See comments about the protocole in the second normalization. *)
  set n1 := int.shift 1 n.
  set n2 := int.shift 2 n.
  (* Now we are under the stairs. *)
  have hn1 : n1%:~R = n%:~R + rat_of_Z 1.
    by rewrite rat_of_ZEdef rmorphD.
  have hn2 : n2%:~R = n%:~R + rat_of_Z 2.
    rewrite !rmorphD /=; rat_field.
  rewrite /v.P_cf0 /v.P_cf1 /v.P_cf2 /v.P_cf3.
  rewrite /v.P_cf4 /v.Q_cf0_0 /v.Q_cf0_1.
  rewrite /v.Q_cf1_0 /v.Sk2_cf0_0 /v.Sk2_cf0_1.
  rewrite /v.Sn2_cf0_0 /v.Sn2_cf0_1 /v.Sn2_cf1_0.
  rewrite /v.SnSk_cf0_0 /v.SnSk_cf0_1 /v.SnSk_cf1_0.
  rewrite hn1 hn2.
  rat_field.
  (* above: Finished transaction in 16. secs (16.761047u,0.s) *)
  move: nge2; clear; goal_to_lia; intlia.
(* Now the normalization of the second part of the expression causes
   no problem. *)
suff around_p_p_eq_0 : pv_S0_S1 + q_S1_S0 + pv_S1_S1 + remP = 0.
  by rewrite -[RHS]around_p_p_eq_0 add0r.
clear around_n_0.
rewrite {}/q_S1_S0 {}/q_S1_1 {}/pv_S1_S1 {}/pv_S0_S1 {}/pv_0_S1.
(* Unrolling the definition of remP *)
rewrite {}/remP [bigop]unlock /=.
(* Avoid backward shifts, as our rewriting rules cannot deal with them. *)
set p := n - 1.
have -> : n = int.shift 1 p. by rewrite /p; intlia.
have hp : (1 : int) <= p by rewrite /p; intlia.
(* We can now clear n. *)
clearbody p; clear n nge2.
(* Unrolling the definition of P. *)
rewrite /punk.horner_seqop /punk.horner_seqop_rec /=.
(* Unrolling the definition of Q. *)
rewrite /v.Q_flat.
(* Just to ease reading, a few abbreviations. *)
set v10 := v (int.shift 1 p) p.
set v01 := v p (int.shift 1 p).
set v20 := v (int.shift 2 p) p.
set v11 := v (int.shift 1 p) (int.shift 1 p).
set v30 := v (int.shift 3 p) p.
set v21 := v (int.shift 2 p) (int.shift 1 p).
set v12 := v (int.shift 1 p) (int.shift 2 p).
set v40 := v (int.shift 4 p) p.
set v31 := v (int.shift 3 p) (int.shift 1 p).
set v22 := v (int.shift 2 p) (int.shift 2 p).
set v50 := v (int.shift 5 p) p.
set v41 := v (int.shift 4 p) (int.shift 1 p).
set v32 := v (int.shift 3 p) (int.shift 2 p).
set v51 := v (int.shift 5 p) (int.shift 1 p).
set v42 := v (int.shift 4 p) (int.shift 2 p).
set v33 := v (int.shift 3 p) (int.shift 3 p).
set v52 := v (int.shift 5 p) (int.shift 2 p).
set v43 := v (int.shift 4 p) (int.shift 3 p).
set v53 := v (int.shift 5 p) (int.shift 3 p).
set v44 := v (int.shift 4 p) (int.shift 4 p).
set v54 := v (int.shift 5 p) (int.shift 4 p).
set v55 := v (int.shift 5 p) (int.shift 5 p).
Fail set vvv := v _ _.
(* Normalization modulo annulators of v. *)
rewrite [v55]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v55} -/v54 -/v53 -/v52 -/v51 -/v50.
rewrite [v54]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v54} -/v53 -/v52 -/v51 -/v50.
rewrite [v53]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v53} -/v52 -/v51 -/v50.
rewrite [v52]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v52} -/v51 -/v50.
rewrite [v44]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v44} -/v43 -/v42 -/v41 -/v40.
rewrite [v43]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v43} -/v42 -/v41 -/v40.
rewrite [v42]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v42} -/v41 -/v40.
rewrite [v33]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v33} -/v32 -/v31 -/v30.
rewrite [v32]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v32} -/v31 -/v30.
rewrite [v22]v_Sk2; last first.
  by rewrite /v.precond.Sk2; goal_to_lia; intlia.
rewrite {v22} -/v21 -/v20.
(* Use v_SnSk and v_Sn2 in alternation: *)
rewrite [v51]v_SnSk; last first.
  by rewrite /v.precond.SnSk; goal_to_lia; intlia.
rewrite {v51} -/v50 -/v40 -/v41.
rewrite [v50]v_Sn2; last first.
  by rewrite /v.precond.Sn2; goal_to_lia; intlia.
rewrite {v50} -/v40 -/v30 -/v31.
rewrite [v41]v_SnSk; last first.
  by rewrite /v.precond.SnSk; goal_to_lia; intlia.
rewrite {v41} -/v40 -/v30 -/v31.
rewrite [v40]v_Sn2; last first.
  by rewrite /v.precond.Sn2; goal_to_lia; intlia.
rewrite {v40} -/v30 -/v20 -/v21.
rewrite [v31]v_SnSk; last first.
  by rewrite /v.precond.SnSk ; goal_to_lia; intlia.
rewrite {v31} -/v30 -/v20 -/v21.
rewrite [v30]v_Sn2; last first.
  by rewrite /v.precond.Sn2; goal_to_lia; intlia.
rewrite {v30} -/v20 -/v10 -/v11.
rewrite [v21]v_SnSk; last first.
  by rewrite /v.precond.SnSk; goal_to_lia; intlia.
(* Now we are under the stair, we unfold the coefficients of the operators *)
(* and call field. *)
rewrite {v21} -/v20 -/v10 -/v11.
(* We inspect the current expression to collect the shifts of p that are *)
(* present and set definitions in normal form. *)
set p1 := int.shift 1 p.
set p2 := int.shift 2 p.
set p3 := int.shift 3 p.
set p4 := int.shift 4 p.
set p5 := int.shift 5 p.
(* We pre-compute the desired expressions for the embeddings in rat of the p* *)
(* that will occur after unfolding the operators. *)
have kp1 : p1%:~R = p%:~R + 1 :> rat by rewrite /p1 int.shift2R.
have kp2 : p2%:~R = p%:~R + rat_of_Z 2 :> rat.
  by rewrite /p1 int.shift2R rat_of_ZEdef.
have kp3 : p3%:~R = p%:~R + rat_of_Z 3 :> rat.
  by rewrite /p1 int.shift2R rat_of_ZEdef.
have kp4 : p4%:~R = p%:~R + rat_of_Z 4 :> rat.
  by rewrite /p1 int.shift2R rat_of_ZEdef.
have kp5 : p5%:~R = p%:~R + rat_of_Z 5 :> rat.
  by rewrite /p1 int.shift2R rat_of_ZEdef.
rewrite /v.P_cf0 /v.P_cf1 /v.P_cf2 /v.P_cf3.
rewrite /v.P_cf4 /v.Q_cf0_0 /v.Q_cf0_1.
rewrite /v.Q_cf1_0 /v.Sk2_cf0_0 /v.Sk2_cf0_1.
rewrite /v.Sn2_cf0_0 /v.Sn2_cf0_1 /v.Sn2_cf1_0.
rewrite /v.SnSk_cf0_0 /v.SnSk_cf0_1 /v.SnSk_cf1_0.
(* These rewriting catch the occurrences of p*%:~R modulo conversion, even *)
(* those that are not folded and display other forms in terms of nested *)
(* shift and shift1, because the head symbols in the rhs of kp* is _%:~R. *)
rewrite kp1 kp2 kp3 kp4 kp5.
rat_field.
(* above: Finished transaction in 157. secs (156.849802u,0.252016s) *)
by move: hp; clear; goal_to_lia; intlia.
Qed.

End AnnOfB.
