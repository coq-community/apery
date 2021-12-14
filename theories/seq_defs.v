(* This file defines the various sequences studied in a proof that
   zeta(3) is irrational.  We mostly follow the names given in the
   Maple session by Chyzak & Salvy, with a notable exception for b:
   the alternative definition below is better suited for
   algorithmically getting a recurrence on b. *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import binomialz bigopz.
Require harmonic_numbers.

(* Partial sum of zeta(3). *)
Definition ghn3 : int -> rat := harmonic_numbers.ghn 3.

Definition c (n k : int) : rat :=
  (binomialz n k)%:Q ^ 2 * (binomialz (n + k) k)%:Q ^ 2.

(* Sequence a of the Maple session: sum of c's. *)
Definition a (n : int) : rat := \sum_(0 <= k < n + 1 :> int) (c n k).

Definition d (n k m : int) : rat :=
  (-1) ^ (m + 1) /
    (2%:Q * m%:Q ^ 3 * (binomialz n m)%:Q * (binomialz (n + m) m)%:Q).

Definition s (n k : int) : rat := \sum_(1 <= m < k + 1 :> int) d n k m.

Definition u (n k : int) : rat := ghn3 n + s n k.

Definition v (n k : int) : rat := c n k * u n k.

(* Alternative definition for the sequence b of the Maple session. *)
Definition b (n : int) : rat := \sum_(0 <= k < n + 1 :> int) v n k.
