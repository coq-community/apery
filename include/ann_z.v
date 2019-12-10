Definition Sn2_cf0 (n_ : int) : rat :=
let n : rat := n_%:~R in
(- rat_of_Z 1 * (n + rat_of_Z 1)^3) / ((n + rat_of_Z 2)^3).

Definition Sn2_cf1 (n_ : int) : rat :=
let n : rat := n_%:~R in
((rat_of_Z 2 * n + rat_of_Z 3) * (n^2 + rat_of_Z 3 * n + rat_of_Z 3)) / ((n + rat_of_Z 2)^3).

Definition Sn2 (z : int -> rat) := forall (n_ : int), precond.Sn2 n_ ->
z (int.shift 2 n_) = Sn2_cf0 n_ * z n_ + Sn2_cf1 n_ * z (int.shift 1 n_).
