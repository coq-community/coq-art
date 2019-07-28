
Definition my_False : Prop := forall P:Prop, P.

Definition my_not (P:Prop) : Prop := P -> my_False.


Theorem not_False : my_not my_False.
Proof.
 intro H; assumption. 
Qed.


Theorem triple_neg : forall P:Prop, my_not (my_not (my_not P)) -> my_not P.
Proof.
 unfold my_not; auto.
Qed.

Theorem P3PQ : forall P Q:Prop, my_not (my_not (my_not P)) -> P -> Q.
Proof.
 intros P Q H p; apply (triple_neg _ H p).
Qed.

Theorem contrap : forall P Q:Prop, (P -> Q) -> my_not Q -> my_not P.
Proof.
 unfold my_not at 2; auto. 
Qed.


Theorem imp_absurd : forall P Q R:Prop, (P -> Q) -> (P -> my_not Q) -> P -> R.
Proof.
 intros P Q R H H0 p; apply (H0 p); auto. 
Qed.
