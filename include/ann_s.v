Require annotated_recs_d.

Definition Sk2_lcomb_cf1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 0.

Definition Sk2_lcomb_cf2 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 0.

Definition Sk2_lcomb_cf3 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 0.

Definition Sk2_lcomb_cf4 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 1.

Definition Sk2_lcomb (s : int -> int -> rat) (n_ k_ : int) : rat :=
Sk2_lcomb_cf1 n_ k_ * annotated_recs_d.P1_flat s n_ k_ + Sk2_lcomb_cf2 n_ k_ * annotated_recs_d.P2_flat s n_ k_ + Sk2_lcomb_cf3 n_ k_ * annotated_recs_d.P3_flat s n_ k_ + Sk2_lcomb_cf4 n_ k_ * annotated_recs_d.P4_flat s n_ k_ .

Require annotated_recs_d.

Definition SnSk_lcomb_cf1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 0.

Definition SnSk_lcomb_cf2 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 0.

Definition SnSk_lcomb_cf3 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 1.

Definition SnSk_lcomb_cf4 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 0.

Definition SnSk_lcomb (s : int -> int -> rat) (n_ k_ : int) : rat :=
SnSk_lcomb_cf1 n_ k_ * annotated_recs_d.P1_flat s n_ k_ + SnSk_lcomb_cf2 n_ k_ * annotated_recs_d.P2_flat s n_ k_ + SnSk_lcomb_cf3 n_ k_ * annotated_recs_d.P3_flat s n_ k_ + SnSk_lcomb_cf4 n_ k_ * annotated_recs_d.P4_flat s n_ k_ .

Require annotated_recs_d.

Definition Sn2_lcomb_cf1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(n + rat_of_Z 2 + k).

Definition Sn2_lcomb_cf2 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 0.

Definition Sn2_lcomb_cf3 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(k * (rat_of_Z 2 * n + rat_of_Z 3) * (n + - k)).

Definition Sn2_lcomb_cf4 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 0.

Definition Sn2_lcomb (s : int -> int -> rat) (n_ k_ : int) : rat :=
Sn2_lcomb_cf1 n_ k_ * annotated_recs_d.P1_flat s n_ k_ + Sn2_lcomb_cf2 n_ k_ * annotated_recs_d.P2_flat s n_ k_ + Sn2_lcomb_cf3 n_ k_ * annotated_recs_d.P3_flat s n_ k_ + Sn2_lcomb_cf4 n_ k_ * annotated_recs_d.P4_flat s n_ k_ .

Definition Sk2_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- rat_of_Z 1 * (k + rat_of_Z 1)^3) / (((k + rat_of_Z 2) * (n + rat_of_Z 2 + k) * (- n + k + rat_of_Z 1))).

Definition Sk2_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(rat_of_Z 2 * k^3 + rat_of_Z 8 * k^2 + rat_of_Z 11 * k + rat_of_Z 5 + - k * n + - k * n^2 + - rat_of_Z 2 * n^2 + - rat_of_Z 2 * n) / (((k + rat_of_Z 2) * (n + rat_of_Z 2 + k) * (- n + k + rat_of_Z 1))).

Definition Sk2 (s : int -> int -> rat) := forall (n_ k_ : int), precond.Sk2 n_ k_ ->
s n_ (int.shift 2 k_) = Sk2_cf0_0 n_ k_ * s n_ k_ + Sk2_cf0_1 n_ k_ * s n_ (int.shift 1 k_).

Definition SnSk_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- n + k) / ((n + rat_of_Z 2 + k)).

Definition SnSk_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
rat_of_Z 1.

Definition SnSk_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(n + - k) / ((n + rat_of_Z 2 + k)).

Definition SnSk (s : int -> int -> rat) := forall (n_ k_ : int), precond.SnSk n_ k_ ->
s (int.shift 1 n_) (int.shift 1 k_) = SnSk_cf0_0 n_ k_ * s n_ k_ + SnSk_cf1_0 n_ k_ * s (int.shift 1 n_) k_ + SnSk_cf0_1 n_ k_ * s n_ (int.shift 1 k_).

Definition Sn2_cf0_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(- rat_of_Z 2 + - rat_of_Z 9 * n^2 + rat_of_Z 3 * k * n + - rat_of_Z 6 * k^2 + - n^4 + - rat_of_Z 5 * n^3 + - rat_of_Z 6 * k^3 + - k * n^3 + k * n^2 + rat_of_Z 4 * k^2 * n^2 + rat_of_Z 2 * k^2 * n + - rat_of_Z 4 * k^3 * n + - k + - rat_of_Z 7 * n) / (((n + rat_of_Z 2)^3 * (n + rat_of_Z 2 + k))).

Definition Sn2_cf1_0 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
((rat_of_Z 2 * n + rat_of_Z 3) * (n^2 + rat_of_Z 3 * n + rat_of_Z 3)) / ((n + rat_of_Z 2)^3).

Definition Sn2_cf0_1 (n_ k_ : int) : rat :=
let n : rat := n_%:~R in
let k : rat := k_%:~R in
(rat_of_Z 2 * k * (rat_of_Z 2 * n + rat_of_Z 3) * (k + rat_of_Z 1) * (- n + k)) / (((n + rat_of_Z 2)^3 * (n + rat_of_Z 2 + k))).

Definition Sn2 (s : int -> int -> rat) := forall (n_ k_ : int), precond.Sn2 n_ k_ ->
s (int.shift 2 n_) k_ = Sn2_cf0_0 n_ k_ * s n_ k_ + Sn2_cf1_0 n_ k_ * s (int.shift 1 n_) k_ + Sn2_cf0_1 n_ k_ * s n_ (int.shift 1 k_).
