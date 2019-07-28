Definition my_False : Prop := forall P:Prop, P.

Definition my_not (P:Prop) : Prop := P -> my_False.

Definition my_and (P Q:Prop) : Prop := forall R:Prop, (P -> Q -> R) -> R.

Definition my_or (P Q:Prop) : Prop :=
  forall R:Prop, (P -> R) -> (Q -> R) -> R.

Definition my_ex (A:Type) (P:A -> Prop) : Prop :=
  forall R:Prop, (forall x:A, P x -> R) -> R.


Theorem my_and_left : forall P Q:Prop, my_and P Q -> P.
Proof.
 intros P Q H; apply H; auto.
Qed.

Theorem my_and_right : forall P Q:Prop, my_and P Q -> Q.
Proof.
 intros P Q H; apply H; auto.
Qed.

Theorem my_and_ind : forall P Q R:Prop, (P -> Q -> R) -> my_and P Q -> R.
Proof.
  intros P Q R H H0; apply H0; assumption.
Qed.


Theorem my_or_introl : forall P Q:Prop, P -> my_or P Q.
Proof.
  unfold my_or; auto.  
Qed.

Theorem my_or_intror : forall P Q:Prop, Q -> my_or P Q.
Proof.
  unfold my_or; auto.  
Qed.

Theorem my_or_ind : forall P Q R:Prop, (P -> R) -> (Q -> R) -> my_or P Q -> R.
Proof.
  intros P Q R H H0 H1; apply H1; assumption.
Qed.

Theorem my_or_False : forall P:Prop, my_or P my_False -> P.
Proof.
 unfold my_False; intros P H; apply H; intro H0; apply H0.
Qed.

Theorem my_or_comm : forall P Q:Prop, my_or P Q -> my_or Q P.
Proof.
 intros P Q H; apply H; intros H0 R; auto.
Qed.


Theorem my_ex_intro : forall (A:Type) (P:A -> Prop) (a:A), P a -> my_ex A P.
Proof.
 intros A P a Ha R H; eapply H; eauto.
Qed.

Theorem my_not_ex_all :
 forall (A:Type) (P:A -> Prop), my_not (my_ex A P) -> forall a:A, my_not (P a).
Proof.
 intros A P H a H';
 apply H; eapply my_ex_intro; eauto.
Qed.




Theorem my_ex_ex : forall (A:Type) (P:A -> Prop), my_ex A P -> ex P.
Proof.
 intros A P H; apply H.
 intros x Hx; exists x; assumption.
Qed.



Theorem ex_my_ex : forall (A:Type) (P:A -> Prop), ex P -> my_ex _ P.
Proof.
 intros A P H; elim H; intros x Hx R.
 intros H0; eapply H0; eapply Hx.
Qed.
