Load "include/ops_header.v".


Module precond.

Definition Sn (n k m : int) := (n >= 0) /\ (m > 0) /\ (n >= m).
Definition Sk (n k m : int) := true.
Definition Sm (n k m : int) := (n > 0) /\ (m > 0) /\ (n > m).

End precond.

Definition not_D1 (n k m : int) := (0 < m) && (m < n).
Definition not_D2 (n k m : int) := (0 < m) && (m < n).
Definition not_D3 (n k m : int) := (0 < m) && (m < n).
Definition not_D4 (n k m : int) := (0 < m) && (m < n).

Load "include/ann_d.v".

Definition CT1  (d : int -> int -> int -> rat) : Prop := forall (n_ k_ m_ : int),
  not_D1 n_ k_ m_ -> P1_horner (punk.pfun2 d m_) n_ k_ = Q1_flat d n_ k_ (int.shift 1 m_) - Q1_flat d n_ k_ m_.

Definition CT2  (d : int -> int -> int -> rat) := forall (n_ k_ m_ : int),
  not_D2 n_ k_ m_ -> P2_horner (punk.pfun2 d m_) n_ k_ = Q2_flat d n_ k_ (int.shift 1 m_) - Q2_flat d n_ k_ m_.

Definition CT3  (d : int -> int -> int -> rat) := forall (n_ k_ m_ : int),
  not_D3 n_ k_ m_ -> P3_horner (punk.pfun2 d m_) n_ k_ = Q3_flat d n_ k_ (int.shift 1 m_) - Q3_flat d n_ k_ m_.

Definition CT4  (d : int -> int -> int -> rat) := forall (n_ k_ m_ : int), 
  not_D4 n_ k_ m_ -> P4_horner (punk.pfun2 d m_) n_ k_ = Q4_flat d n_ k_ (int.shift 1 m_) - Q4_flat d n_ k_ m_.

Record Ann d : Type := ann {
  Sn_  : Sn d;
  Sk_  : Sk d;
  Sm_  : Sm d
}.

