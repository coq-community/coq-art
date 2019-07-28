Require Import Arith.

Fixpoint mult2 (n:nat) : nat :=
  match n with
  | O => 0
  | S p => S (S (mult2 p))
  end.


Lemma mult2_double : forall n:nat, mult2 n = n + n.
Proof.
 intro n; elim n; simpl; auto.
 -  intros n0 H; rewrite H; now rewrite <- plus_n_Sm.
Qed.




