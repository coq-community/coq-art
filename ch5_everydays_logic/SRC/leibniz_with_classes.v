Require Import RelationClasses Setoid.
Import Relation_Definitions.

Section leibniz.
 Variable A : Type.
 

 Definition leibniz (a b:A) : Prop := forall P:A -> Prop, P a -> P b.

 Global Instance leibniz_sym : Symmetric  leibniz.
 Proof.
  intros a b H Q;  apply H; trivial.
 Qed.

 Global Instance  leibniz_refl : Reflexive  leibniz.
 Proof.
  intros a P; trivial.
 Qed.

 Global Instance leibniz_trans : Transitive  leibniz.
 Proof.
  intros x y z Hxy Hyz; unfold leibniz; intros P H.
  apply Hyz;  apply Hxy; assumption.
 Qed.


 Global Instance leibniz_equiv : Equivalence leibniz.
 Proof.
  split.
  - apply leibniz_refl.
  - apply leibniz_sym. 
  - apply leibniz_trans. 
  Qed.


 Theorem leibniz_least :
  forall R:relation A, reflexive A R -> inclusion A leibniz R.
 Proof.
  intros R H x y H0; apply H0; apply H.
 Qed.


 Theorem leibniz_eq : forall a b:A, leibniz a b -> a = b.
 Proof.
  intros a b H; now apply H.
 Qed.


 Theorem eq_leibniz : forall a b:A, a = b -> leibniz a b.
 Proof.
  intros a b e; rewrite e;  reflexivity.
 Qed.

 Theorem leibniz_ind :
  forall (x:A) (P:A -> Prop), P x -> forall y:A, leibniz x y -> P y.
 Proof.
  intros x P H y Hy;now apply Hy.
 Qed.


End leibniz.

