Require Import ssreflect ssrfun ssrbool conj.


Lemma test_andb_to_and_low_level_4 b1 b2 b3 b4 : b1 && b2 && b3 && b4 -> True.
Proof.
rewrite Private.and_bootstrap.
rewrite !Private.and_eat_one.
rewrite -Private.andb_iter_cons_cons.
move/Private.and_iterP.
rewrite /=.
done.
Qed.

Lemma test_andb_to_and_4 b1 b2 b3 b4 : b1 && b2 && b3 && b4 -> True.
Proof.
andb_to_and.
done.
Qed.


Lemma test_andb_to_and_low_level_3 b1 b2 b3 : b1 && b2 && b3 -> True.
Proof.
rewrite Private.and_bootstrap.
rewrite !Private.and_eat_one.
rewrite -Private.andb_iter_cons_cons.
move/Private.and_iterP.
rewrite /=.
done.
Qed.

Lemma test_andb_to_and_3 b1 b2 b3 : b1 && b2 && b3 -> True.
Proof.
andb_to_and.
done.
Qed.


Lemma test_andb_to_and_low_level_2 b1 b2 : b1 && b2 -> True.
Proof.
rewrite Private.and_bootstrap.
rewrite ?Private.and_eat_one.
rewrite -Private.andb_iter_cons_cons.
move/Private.and_iterP.
rewrite /=.
done.
Qed.

Lemma test_andb_to_and_2 b1 b2 : b1 && b2 -> True.
Proof.
andb_to_and.
done.
Qed.
