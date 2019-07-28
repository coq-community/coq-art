Lemma id_P : forall P:Prop, P -> P.
Proof.
 auto.
Qed.

Lemma id_PP : forall P:Prop, (P -> P) -> P -> P.
Proof.
 auto.
Qed.

Lemma imp_trans : forall P Q R:Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
 auto.
Qed.

Lemma imp_perm : forall P Q R:Prop, (P -> Q -> R) -> Q -> P -> R.
Proof.
 auto.
Qed.

Lemma ignore_Q : forall P Q R:Prop, (P -> R) -> P -> Q -> R.
Proof.
 auto.
Qed.

Lemma delta_imp : forall P Q:Prop, (P -> P -> Q) -> P -> Q.
Proof.
 auto.
Qed.

Lemma delta_impR : forall P Q:Prop, (P -> Q) -> P -> P -> Q.
Proof.
 auto.
Qed.

Lemma losange :
 forall P Q R S:Prop, (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
Proof.
 auto.
Qed. 

Lemma weak_peirce : forall P Q:Prop, ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
 auto.
Qed.
