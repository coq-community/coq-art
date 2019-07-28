Require Import JMeq.

Lemma plus_assoc_JM : forall n p q:nat,
                       JMeq (n+(p+q)) (n+p+q).
Proof.
 induction n; simpl.
 -  split.
 -  intros p q; pattern (n+p+q). 
    eapply JMeq_ind.
    +  apply JMeq_refl.
    +  auto.
Qed.


