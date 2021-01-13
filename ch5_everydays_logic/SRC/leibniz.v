Require Import Relations.
Section leibniz.
 Variable A : Type.
 

 Definition leibniz (a b:A) : Prop := forall P:A -> Prop, P a -> P b.

 Theorem leibniz_sym : symmetric A leibniz.
 Proof.
  intros a b H Q; apply H; trivial.
 Qed.

 Theorem leibniz_refl : reflexive A leibniz. 
 Proof.
  intros a P; trivial.
 Qed.



 Theorem leibniz_trans : transitive A leibniz.
 Proof.
  intros x y z Hxy Hyz; unfold leibniz; intros P H.
  apply Hyz;  apply Hxy; assumption.
 Qed.


 #[local] Hint Resolve leibniz_trans leibniz_sym leibniz_refl : core.

 Theorem leibniz_equiv : equiv A leibniz.
 Proof.
  now repeat split. 
 Qed.


 Theorem leibniz_least :
  forall R:relation A, reflexive A R -> inclusion A leibniz R.
 Proof.
  intros R H x y H0; apply H0; apply H.
 Qed.


 Theorem leibniz_eq : forall a b:A, leibniz a b -> a = b.
 Proof.
  intros a b H;   now apply H.
 Qed.

 Theorem eq_leibniz : forall a b:A, a = b -> leibniz a b.
 Proof.
  intros a b e; rewrite e; unfold leibniz; auto.
 Qed.

 Theorem leibniz_ind :
  forall (x:A) (P:A -> Prop), P x -> forall y:A, leibniz x y -> P y.
 Proof.
  intros x P H y Hy; now apply Hy.
 Qed.


End leibniz.

