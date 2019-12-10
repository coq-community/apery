Require Import ZArith.
Require Import Field.

From mathcomp Require Import all_ssreflect all_algebra.

Require Import rat_of_Z.
Export rat_of_Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

(* In this file we craft automated decision procedures for equalities in type *)
(* rat, modulo the structure of field. We do this is two steps:               *)
(*   i) we define  custom ring/fields tactics using an opaque cast for        *)
(*     numeral constants. This optimizes the normalisation of expressions     *)
(*     featuring "large" numeral constants by optimizing the                  *)
(*     reification/interpretation steps.                                      *)
(*   ii) we wrap this tactic is a preprocessing code, which accomodates       *)
(*     expressions of type convertible but non syntactically equal to rat.    *)
(*    This is typical of the use of the ssralg generic structures.            *)

(* Declaration of customized ring and field tactics for the rat datatype. *)

Lemma rat_morph_Z :
  ring_morph
    zeroq oneq addq mulq subq oppq (@eq rat)
    Z0 (Zpos xH) Zplus Zmult Zminus Z.opp Zeq_bool
    rat_of_Z.
Proof.
pose R := [unitRingType of rat].
rewrite -[zeroq]/(@GRing.zero R) -[oneq]/(@GRing.one R).
rewrite -[addq]/(@GRing.add R) -[mulq]/(@GRing.mul R).
rewrite -[subq]/(fun x y => @GRing.add R x (@GRing.opp R y)).
rewrite -[oppq]/(@GRing.opp R) /R{R}.
split; rewrite rat_of_ZEdef => //; case=> [|a|a]; try case=> [|b|b] //=; 
  rewrite ?addr0 ?add0r ?sub0r ?mulr0 ?mul0r ?rat_of_Z_neg ?opprK //;
  rewrite ?mulrNN 1?[_ * - _]mulrC ?mulNr -1?opprB ?opprK -1?Z.pos_sub_opp ?rat_of_Z_opp;
  try congr (- _);
  rewrite ?rat_of_Z_add // 1?addrC //;
  rewrite ?rat_of_Z_mul // 1?mulrC //;
  rewrite ?rat_of_Z_sub // ?opprB // 1?addrC //.
  by move/Zeq_bool_eq->.
by move/Zeq_bool_eq=> [->].
Qed.

(* Make the reification process know about the rat_of_Z cast *)
Ltac Zcst t :=
  match t with
  | rat_of_Z ?u => constr:(u)
  | oneq => constr:(Zpos xH)
  | zeroq => constr:(Z0)
  | _ => constr:(InitialRing.NotConstant)
  end.

(* Actual registration of the ring/field structures *)
Add Field rat_Zfield :
  rat_field_theory
    (morphism rat_morph_Z,
     constants [Zcst]).

(* Preprocessing of an equality between two terms of type rat but which      *)
(* involves arbitrary rat instances of the generic ssralg structures.        *)
(* Since reification is syntactic we first convert both handsides to a 'flat'*)
(* normal form version, using only the datas of the rat field (rat, oneq,    *)
(* addq,...). We also unroll power to multiplications as we did not manage   *)
(* to deal with this properly with the customizations of the ring/field      *)
(* tactic. *)

Fixpoint powq (r : rat) (n : nat) :=
  match n with
  | 0 => oneq
  | 1 => r
  | m.+1 => mulq r (powq r m)
  end.

Ltac transf_unary transf x concr_op :=
  let t := transf x in constr:(concr_op t).

Ltac transf_binary transf x1 x2 concr_op :=
  let t1 := transf x1 in let t2 := transf x2 in constr:(concr_op t1 t2).

Definition NothingHappened := false.

(* Pure generic constructs. *)
Ltac generic_transf transf t :=
  match t with
  | (@GRing.mul ?any_struct) ?x1 ?x2 =>
      let res := transf_binary transf x1 x2 mulq in constr:(res)
  | (@GRing.add ?any_struct) ?x1 ?x2 =>
      let res := transf_binary transf x1 x2 addq in constr:(res)
  | (@GRing.opp ?any_struct) ?x =>
      let res := transf_unary transf x oppq in constr:(res)
  | (@GRing.inv ?any_struct) ?x =>
      let res := transf_unary transf x invq in constr:(res)
  | GRing.one ?any_struct => constr:(oneq) (* 1 in any_struct as a ring. *)
  | GRing.zero ?any_struct => constr:(zeroq) (* 0 in any_struct as a ring. *)
  | @exprz ?any_thing ?x1 ?x2 =>
       match x2 with
       | Posz ?n => let t1 := transf x1 in constr:(powq t1 n)
       end
  | _ => constr:(NothingHappened)
  end.

(* Given t supposed to be in int, output the rat_transf of t%:~R. *)
(* Warning this performs transformations that are not provable by *)
(* convertibity so we do not call this code and only leave it for *)
(* the record.*)
Ltac int_to_rat_transf r1 r2 t :=
  let res := generic_transf ltac:(int_to_rat_transf r1 r2) t in
    match res with
    | NothingHappened => constr:(@intmul r1 (GRing.one r2) t)
    | _ => constr:(res)
    end.

(* Given an expression t in the generic rat ring, generate its translation
   in rat using concrete operations in rat. *)
Ltac rat_transf t :=
  let res := generic_transf rat_transf t in
    match res with
    | NothingHappened =>
      match t with
      (* Catch generic expression of type int embedded in rat. *)
      | @intmul ?rat_thing1 (GRing.one ?rat_thing2) ?any_int =>
        (* Expand 5%:~R into 1%Q + (0%Q + 1%Q + ... + 1%Q) and the like.*)
        match any_int with
        | Posz 0 => constr:(zeroq)
        | Posz 1 => constr:(oneq)
        | GRing.one ?any_struct => constr:(oneq)
        | GRing.zero ?any_struct => constr:(zeroq)
        | Posz (S ?n) =>
            let y := constr:((Posz n)%:~R : rat) in
              let t := rat_transf y in constr:(addq t oneq)
        (* Simplify (n^0)%:~R into oneq and rec call rat_transf on n%:~R on*)
        (* n^1%:~R *)  
        | @exprz ?any_thing ?x1 ?x2 =>
            match x2 with
              | Posz 0 => constr:(oneq)
              | Posz 1 =>
                let y := constr:(@intmul rat_thing1 (GRing.one rat_thing2) x1) in
                let t := rat_transf y in constr:(t)
              | _ => constr:(t)            
            end
        | _ => constr:(t)
            (* This alternative code would allow transformation under a _%:~R*)
             (*  that are valid but not provable by conversion: *)
            (* let new_int := *)
                  (* int_to_rat_transf rat_thing1 rat_thing2 any_int in *)
            (*   constr:new_int *)
        end
      (* Catch inverses in the form x^-1. *)
      | @exprz ?rat_thing1 ?x
            (@GRing.opp ?rat_thing2 (GRing.one ?rat_thing3)) =>
          let t := rat_transf x in constr:(invq t)
      | _ => constr:(t)
      end
    | _ => constr:(res)
    end.

(* Reduction of elaborated instances of rat to a mere rat *)
Ltac to_rat_type := 
  rewrite -?[GRing.Ring.sort _]/rat;
  rewrite -?[GRing.Zmodule.sort _]/rat;
  rewrite -?[Equality.sort (GRing.Zmodule.eqType _)]/rat;
  rewrite -?[Equality.sort (GRing.Ring.eqType _)]/rat.

(* The prefield tactic operates on a goal which is an equality between *)
(* two terms in rat. It reduces the type of the equality to 'rat, *)
(* applies the previous rat_transf transformation to *)
(* both handsides and proves these modifications by reflexivity. *)
(* After a successful run of the tactic, we get a new version of the initial *)
(* goal ready for normalization, almost. *)

(* At last step: the 'symmetry' before the second reflexivity *)
(* optimizes the conversion due to the heuristic applied by reflexivity *)
(* which reduces the left hand side first. *)

Ltac prefield := 
  match goal with
  | |- ?x1 = ?x2 =>
    let t1 := rat_transf x1 in let t2 := rat_transf x2 in
    let lhs := fresh "lhs" in
    let rhs := fresh "rhs" in
      (* now we should reduce also by hand the type hidden in (@eq) *)
      to_rat_type;
      pose lhs := (t1 : rat); unfold powq in lhs;
      pose rhs := (t2 : rat); unfold powq in rhs;
      transitivity lhs; unfold lhs; clear lhs;
      [ reflexivity
      | transitivity rhs; unfold rhs; clear rhs;
        [| symmetry; reflexivity ] ] 
end.

(* In our case, the uniterpreted terms in a goal to which we apply ring/field *)
(* are integers variables embedded in rat. We make sure that all the *)
(* convertible occurrences of a same variable share the same symbol to ensure *)
(* that the reification behaves well and avoid silly incompleteness.*)
(* Note that we carefully re-cast the pattern to the mere rat to avoid Coq *)
(* expanding an elaborated instance of ssralg structure...*)

Ltac catch_embedded := let emb := fresh "emb" in set emb := ((_)%:~R : rat).
          
(* Due to a current incompleteness of the ring/field tactic, we need to make *)
(* sure that all occurrences of zeroq (resp. oneq) are in fact under the form *)
(* of rat_of_Z 0 (resp. rat_of_Z 1). This would not be needed in the case of *)
(* convertible values, but here these are only provable equalities because *)
(* we locked rat_of_Z. Fixed in coq trunk. *)

Ltac patch_incomplete_field := rewrite ?rat_of_Z_0  ?rat_of_Z_1.

(* We finally gather all the ingredients in a single tactic. *)
(* The last rewrite operation would better be part of the intlia tactic.*)
Ltac rat_field := 
prefield; 
patch_incomplete_field; 
repeat catch_embedded; 
field;
rewrite ?rat_of_ZEdef /=.

Ltac rat_field_simplify := 
prefield; 
patch_incomplete_field; 
repeat catch_embedded; 
field_simplify;
rewrite ?rat_of_ZEdef /=.
