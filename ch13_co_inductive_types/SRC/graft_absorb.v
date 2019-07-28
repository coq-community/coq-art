Require Export LTree_bisimilar.

Set Implicit Arguments.

Theorem graft_absorb {A:Type}: forall t1 t2: LTree A, 
                       EveryInf t1 ->
                       LTree_bisimilar t1 (graft t1 t2).
Proof.
 cofix H.
 intros  t1 t2; case t1.
 -  inversion_clear 1.
 -  intros a t'1 t'2 H0 ; rewrite graft_unfold2.
    inversion_clear H0; right; auto.
Qed.

