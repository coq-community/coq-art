Require Import Arith.

Fixpoint div3 (n:nat): nat :=
  match n with
    | 0 | 1 | 2 => 0
    | S (S (S p)) => S (div3 p)
  end.

Lemma nat_ind3 (P : nat -> Prop) :
  P 0 -> P 1 -> P 2 ->
  (forall i:nat, P i -> P (3 + i)) ->
  forall n:nat, P n.
Proof.
 intros H0 H1 H2 HS n.
 assert (H :P n /\ P (S n) /\ P (S (S n))).
 induction n.
 split;auto.
 destruct IHn as [Hn [HSn HSSn]];repeat split;auto.
 - apply HS;auto.
 -  tauto.
Qed.

Lemma div3_le : forall n, div3 n <= n.
Proof. 
induction n using nat_ind3; auto.
 - simpl; apply le_trans with (S n);auto with arith.
Qed.


