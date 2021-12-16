Load "include/ops_header.v".

Module precond.

Definition Sn2 (n k : int) := (0 <= k) /\ (k < n).
Definition SnSk (n k : int) := (0 <= k) /\ (k < n).
Definition Sk2 (n k : int) := (0 <= k) /\ (k + 1 < n).

End precond.

Load "include/ann_s.v".

Record Ann s : Type := ann {
  Sn2_ : Sn2 s;
  SnSk_ : SnSk s;
  Sk2_ : Sk2 s
}.
