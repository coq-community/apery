Require annotated_recs_v.

Definition Sn4_lcomb_cf1 (n_ : int) : rat :=
let n : rat := n_%:~R in
rat_of_Z 1.

Definition Sn4_lcomb (b : int -> rat) (n_ : int) : rat :=
Sn4_lcomb_cf1 n_ * annotated_recs_v.P_flat b n_ .
