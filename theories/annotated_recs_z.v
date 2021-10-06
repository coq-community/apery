Load "include/ops_header.v".

(* These preconditions are temporarily set to True, and will be refined
   by the very process of formalization. *)
Module precond.

Definition Sn2 (n : int) := (n != - 2%:~R) /\ (n != - 1).

End precond.

Load "include/ann_z.v".

Record Ann z : Type := ann {
  Sn2_ : Sn2 z
}.
