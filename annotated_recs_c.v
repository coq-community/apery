Load "include/ops_header.v".

Module precond.

Definition Sn (n k : int) := (k != n + 1) /\ (n != -1).

Definition Sk (n k : int) := (k + 1 != 0) /\ (n != 0).

End precond.

Definition not_D (n k : int) := (n >= 0) && (k >= 0) && (k < n).

Load "include/ann_c.v".

Definition CT (c : int -> int -> rat) := forall (n_ k_ : int), not_D n_ k_ -> 
P_horner (c ^~ k_) n_ = Q_flat c n_ (int.shift 1 k_) - Q_flat c n_ k_.

Record Ann c : Type := ann {
  Sn_ : Sn c;
  Sk_ : Sk c
}.

