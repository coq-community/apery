From mathcomp Require Import all_ssreflect.



Module Private.

Fixpoint andb_iter (l : seq bool) :=
  match l with
  | nil => true
  | b :: nil => b
  | b :: l' => b && andb_iter l'
  end.

Fixpoint and_iter (l : seq Prop) :=
  match l with
  | nil => True
  | P :: nil => P
  | P :: l' => P /\ and_iter l'
  end.

Lemma andb_iter_nil : andb_iter nil = true.
Proof.  by [].  Qed.
Lemma andb_iter_singleton b : andb_iter (b :: nil) = b.
Proof.  by [].  Qed.
Lemma andb_iter_cons_cons a b l :
   andb_iter (a :: b :: l) = a && andb_iter (b :: l).
Proof.  by elim: l.  Qed.

Definition andb_iterE :=
  (andb_iter_nil, andb_iter_singleton, andb_iter_cons_cons).

Lemma and_iter_nil : and_iter nil = True.
Proof.  by [].  Qed.
Lemma and_simpl2 P : and_iter (P :: nil) = P.
Proof.  by [].  Qed.
Lemma and_simpl3 P Q l : and_iter (P :: Q :: l) = (P /\ and_iter (Q :: l)).
Proof.  by elim: l.  Qed.

Definition and_iterE := (and_iter_nil, and_simpl2, and_simpl3).

Lemma and_iterP l : reflect (and_iter (map is_true l)) (andb_iter l).
Proof.
elim: l => [/= | a l]; first exact (ReflectT _ I).
case: l => [_ | b l' h]; rewrite !andb_iterE !map_cons !and_iterE.
  exact idP.
by apply: (iffP andP); case=> ha hyp; split => //; apply/h.
Qed.

Lemma and_bootstrap b1 b2 : b1 && b2 = b1 && andb_iter (b2 :: nil).
Proof.  by [].  Qed.

Lemma and_eat_one b1 b2 l :
  b1 && b2 && andb_iter l = b1 && (andb_iter (b2 :: l)).
Proof.
rewrite -andbA.
congr (_ && _).
case: l; first by case: b2.
move=> a l.
by rewrite andb_iter_cons_cons.
Qed.

End Private.


(* Convert a premise given in the form (b1 && ... && bn) to the form
   (b1 /\ ... /\ bn). *)
Ltac andb_to_and :=
  rewrite Private.and_bootstrap;
  rewrite ?Private.and_eat_one;
  rewrite -Private.andb_iter_cons_cons;
  move/Private.and_iterP => /=.
