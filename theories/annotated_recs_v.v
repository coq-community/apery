Load "include/ops_header.v".

Module precond.

Definition Sn2 (n k : int) := (0 <= k) /\ (k < n).
Definition SnSk (n k : int) := (0 <= k) /\ (k < n).
Definition Sk2 (n k : int) := (0 <= k) /\ (k + 1 < n).

End precond.

Definition not_D (n k : int) := (k + 1 < n) && (k > 0) && (n >= 0).

Load "include/ann_v.v".

Definition CT  (v : int -> int -> rat) : Prop := forall (n_ k_ : int),
  not_D n_ k_ -> P_horner (v ^~ k_) n_ = Q_flat v n_ (int.shift 1 k_) - Q_flat v n_ k_.

Record Ann v : Type := ann {
  Sn2_ : Sn2 v;
  SnSk_ : SnSk v;
  Sk2_ : Sk2 v
}.
