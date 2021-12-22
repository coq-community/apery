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
rewrite /v.CT => n k; rewrite /v.not_D => notD.
rewrite /v.P_horner /v.P_seq /punk.horner_seqop /= /v.Q_flat.
do 5! (rewrite v_Sn2; last by rewrite /v.precond.Sn2; lia).
rewrite v_SnSk; last by rewrite /v.precond.SnSk; lia.
rewrite v_Sk2; last by rewrite /v.precond.Sk2; lia.
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
by field; ring_lia.
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
  rewrite big_mkcond /= big_int_recl /=; last lia.
  rewrite ifT; last lia.
  have hn : n = (n - 1 - 1) + 1 + 1 by lia.
  rewrite {1}[in LHS]hn.
  rewrite big_int_recr /=; last lia.
  rewrite ifT; last lia.
  rewrite big_int_recr /=; last lia.
  rewrite ifT; last lia.
  rewrite -hn [n - 1 - 1 + 1]addrNK -big_mkcond big_int_cond big_pred0
      => [ | i].
    by rewrite add0r addrA.
  lia.
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
  rewrite /L; ring.
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
  rewrite [c40]v_Sn2; last by rewrite /v.precond.Sn2; lia.
  rewrite {c40} -/c30 -/c20 -/c21.
  rewrite [c30]v_Sn2; last by rewrite /v.precond.Sn2; lia.
  rewrite {c30} -/c20 -/c11 -/c10.
  rewrite [c21]v_SnSk; last by rewrite /v.precond.SnSk; lia.
  rewrite {c21} -/c11 -/c20 -/c10.
  rewrite [c20]v_Sn2; last by rewrite /v.precond.Sn2; lia.
  rewrite {c20} -/c00 -/c10 -/c01.
  rewrite [c02]v_Sk2; last by rewrite /v.precond.Sk2; lia.
  rewrite {c02} -/c00 -/c01.
  rewrite [c11]v_SnSk; last by rewrite /v.precond.SnSk; lia.
  rewrite {c11} -/c00 -/c01 -/c10.
 (* See comments about the protocole in the second normalization. *)
  set n1 := int.shift 1 n.
  set n2 := int.shift 2 n.
  (* Now we are under the stairs. *)
  have hn1 : n1%:Q = n%:Q + 1%:Q by rewrite rmorphD.
  have hn2 : n2%:Q = n%:Q + 2%:Q by rewrite !rmorphD /=; ring.
  rewrite /v.P_cf0 /v.P_cf1 /v.P_cf2 /v.P_cf3.
  rewrite /v.P_cf4 /v.Q_cf0_0 /v.Q_cf0_1.
  rewrite /v.Q_cf1_0 /v.Sk2_cf0_0 /v.Sk2_cf0_1.
  rewrite /v.Sn2_cf0_0 /v.Sn2_cf0_1 /v.Sn2_cf1_0.
  rewrite /v.SnSk_cf0_0 /v.SnSk_cf0_1 /v.SnSk_cf1_0.
  rewrite {n1}hn1 {n2}hn2.
  field; ring_lia.
  (* above: Finished transaction in 16. secs (16.761047u,0.s) *)
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
have -> : n = int.shift 1 p. by rewrite /p; lia.
have hp : (1 : int) <= p by rewrite /p; lia.
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
rewrite [v55]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v55} -/v54 -/v53 -/v52 -/v51 -/v50.
rewrite [v54]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v54} -/v53 -/v52 -/v51 -/v50.
rewrite [v53]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v53} -/v52 -/v51 -/v50.
rewrite [v52]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v52} -/v51 -/v50.
rewrite [v44]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v44} -/v43 -/v42 -/v41 -/v40.
rewrite [v43]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v43} -/v42 -/v41 -/v40.
rewrite [v42]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v42} -/v41 -/v40.
rewrite [v33]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v33} -/v32 -/v31 -/v30.
rewrite [v32]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v32} -/v31 -/v30.
rewrite [v22]v_Sk2; last by rewrite /v.precond.Sk2; lia.
rewrite {v22} -/v21 -/v20.
(* Use v_SnSk and v_Sn2 in alternation: *)
rewrite [v51]v_SnSk; last by rewrite /v.precond.SnSk; lia.
rewrite {v51} -/v50 -/v40 -/v41.
rewrite [v50]v_Sn2; last by rewrite /v.precond.Sn2; lia.
rewrite {v50} -/v40 -/v30 -/v31.
rewrite [v41]v_SnSk; last by rewrite /v.precond.SnSk; lia.
rewrite {v41} -/v40 -/v30 -/v31.
rewrite [v40]v_Sn2; last by rewrite /v.precond.Sn2; lia.
rewrite {v40} -/v30 -/v20 -/v21.
rewrite [v31]v_SnSk; last by rewrite /v.precond.SnSk; lia.
rewrite {v31} -/v30 -/v20 -/v21.
rewrite [v30]v_Sn2; last by rewrite /v.precond.Sn2; lia.
rewrite {v30} -/v20 -/v10 -/v11.
rewrite [v21]v_SnSk; last by rewrite /v.precond.SnSk; lia.
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
have kp1 : p1%:Q = p%:Q + 1 by rewrite int.shift2R.
have kp2 : p2%:Q = p%:Q + 2%:Q by rewrite int.shift2R.
have kp3 : p3%:Q = p%:Q + 3%:Q by rewrite int.shift2R.
have kp4 : p4%:Q = p%:Q + 4%:Q by rewrite int.shift2R.
have kp5 : p5%:Q = p%:Q + 5%:Q by rewrite int.shift2R.
rewrite /v.P_cf0 /v.P_cf1 /v.P_cf2 /v.P_cf3.
rewrite /v.P_cf4 /v.Q_cf0_0 /v.Q_cf0_1.
rewrite /v.Q_cf1_0 /v.Sk2_cf0_0 /v.Sk2_cf0_1.
rewrite /v.Sn2_cf0_0 /v.Sn2_cf0_1 /v.Sn2_cf1_0.
rewrite /v.SnSk_cf0_0 /v.SnSk_cf0_1 /v.SnSk_cf1_0.
(* These rewriting catch the occurrences of p*%:~R modulo conversion, even *)
(* those that are not folded and display other forms in terms of nested *)
(* shift and shift1, because the head symbols in the rhs of kp* is _%:~R. *)
rewrite {p1}kp1 {p2}kp2 {p3}kp3 {p4}kp4 {p5}kp5.
field; ring_lia.
(* above: Finished transaction in 157. secs (156.849802u,0.252016s) *)
Qed.

End AnnOfB.
