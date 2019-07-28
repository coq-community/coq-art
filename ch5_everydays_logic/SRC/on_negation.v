(** Instance of identity on propositions *)

Theorem not_False : ~ False.
Proof.  unfold not; trivial.  Qed.

Definition  not_False' : ~ False :=
 fun H => H.

Theorem triple_neg : forall P:Prop, ~ ~ ~ P -> ~ P.
Proof.  auto. Qed.

Theorem P3PQ : forall P Q:Prop, ~ ~ ~ P -> P -> Q.
Proof. tauto. Qed.

(** instance of the transivity of -> 
*)
Theorem contrap : forall P Q:Prop, (P -> Q) -> ~ Q -> ~ P.
Proof. auto. Qed.

Theorem imp_absurd : forall P Q R:Prop, (P -> Q) -> (P -> ~ Q) -> P -> R.
Proof.  tauto. Qed.

