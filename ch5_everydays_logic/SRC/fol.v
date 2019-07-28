Section A_declared.
 Variables (A : Set) (P Q : A -> Prop) (R : A -> A -> Prop).

 Theorem all_comm : (forall a b:A, R a b) -> forall a b:A, R b a.
 Proof.
  intros H a b; apply H.
 Qed.

 Theorem all_imp_dist :
  (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
 Proof.
  intros H H0 a; apply H; apply H0.
 Qed.

 Theorem all_delta : (forall a b:A, R a b) -> forall a:A, R a a.
 Proof.
   intros H a; apply H.
 Qed.

End A_declared.