
Require Import Omega.

Lemma le_lt_S_eq : forall n p:nat, n <= p -> p < S n -> n = p.
Proof.
 intros; omega.
Qed.

Lemma twice_n_le_1 : forall n :nat, 2 * n  < 2 ->   n = 0.
Proof.
 intros; omega.
Qed.



Lemma L3n2p : forall n p : nat, p < n -> 3 * n <> 2 * p.
Proof.
 intros;omega.
Qed.
