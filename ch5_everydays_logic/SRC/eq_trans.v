
Theorem eq_trans : forall (A:Type) (a b c:A), a = b -> b = c -> a = c.
Proof.
 intros A a b c H; pattern b;  now apply (eq_ind   a ).
 Qed.

Theorem eq_trans' (A:Type): forall a b c : A, a = b -> b = c -> a = c.
Proof.
 intros  a b c H; now rewrite H.
Qed.


Theorem eq_trans'' (A:Type) :  forall a b c : A, a = b -> b = c -> a = c.
Proof.
 intros  a b c H H0; now rewrite <- H0.
Qed.

