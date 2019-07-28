Lemma and_assoc : forall A B C:Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
 intros A B C [a [b c]]; repeat split; assumption.
Qed.


Lemma and_imp_dist : forall A B C D:Prop,
   (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
Proof.
 tauto.
Qed.


Lemma not_contrad : forall A : Prop, ~(A /\ ~A).
Proof.
 tauto.
Qed.

Lemma or_and_not : forall A B : Prop, (A\/B)/\~A -> B.
Proof.
 tauto.
Qed.


