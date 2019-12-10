Definition Sn_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((n + rat_of_Z 1 + k)^2) / ((- n + - rat_of_Z 1 + k)^2).

Definition Sn (c : int -> int -> rat) := forall (n_ k_ : int), precond.Sn n_ k_ ->
c (int.shift 1 n_) k_ = Sn_cf0_0 n_ k_ * c n_ k_.

Definition Sk_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((- n + k)^2 * (n + rat_of_Z 1 + k)^2) / ((k + rat_of_Z 1)^4).

Definition Sk (c : int -> int -> rat) := forall (n_ k_ : int), precond.Sk n_ k_ ->
c n_ (int.shift 1 k_) = Sk_cf0_0 n_ k_ * c n_ k_.

Definition P_cf0 (n_ : int) : rat :=
let n : rat := n_%:~R in
(n + rat_of_Z 1)^3.

Definition P_cf1 (n_ : int) : rat :=
let n : rat := n_%:~R in
(- rat_of_Z 1 * (rat_of_Z 17 * n^2 + rat_of_Z 51 * n + rat_of_Z 39) * (rat_of_Z 2 * n + rat_of_Z 3)).

Definition P_cf2 (n_ : int) : rat :=
let n : rat := n_%:~R in
(n + rat_of_Z 2)^3.

Definition P_flat (c : int -> rat) (n_ : int) : rat :=
P_cf0 n_ * c n_ + P_cf1 n_ * c (int.shift 1 n_) + P_cf2 n_ * c (int.shift 2 n_).

Definition P_seq := [:: P_cf0; P_cf1; P_cf2].

Definition P_horner := punk.horner_seqop P_seq.

Definition Q_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(rat_of_Z 4 * k^4 * (rat_of_Z 2 * n + rat_of_Z 3) * (- rat_of_Z 4 * n^2 + - rat_of_Z 12 * n + - rat_of_Z 8 + - rat_of_Z 3 * k + rat_of_Z 2 * k^2)) / (((- n + - rat_of_Z 1 + k)^2 * (k + - n + - rat_of_Z 2)^2)).

Definition Q_flat (c : int -> int -> rat) (n_ k_ : int) : rat :=
Q_cf0_0 n_ k_ * c n_ k_.

Definition Q_seq := [:: [:: Q_cf0_0]].

Definition Q_horner := punk.biv_horner_seqop2 Q_seq.
