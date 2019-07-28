Require Import Arith.
Fixpoint sum_n (n:nat) : nat :=
  match n with
  | O => 0
  | S p => S p + sum_n p
  end.

Require Import ArithRing.

Theorem sum_closed_form : forall n:nat, 2 * sum_n n = n * S n.
Proof.
 induction n as [ | p IHp].
 - reflexivity.
 -   simpl sum_n.
     ring_simplify in IHp; ring_simplify. 
     rewrite IHp;ring.
Qed.

Theorem sum_n_le_n : forall n:nat, n <= sum_n n.
Proof.
 induction n as [| p Hp];simpl;auto with arith.
Qed.

