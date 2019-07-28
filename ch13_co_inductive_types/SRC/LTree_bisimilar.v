Require Export Tree_Inf  RelationClasses.

Set Implicit Arguments.

Section LTree_bisimilar_def.
Variable A:Type.

(* An extensional equality on (LTree A) *)

CoInductive LTree_bisimilar :  LTree A -> LTree A -> Prop :=
  LTree_bisimilar_leaf : LTree_bisimilar LLeaf LLeaf
| LTree_bisimilar_bin : forall (a:A) (t1 t'1 t2 t'2 : LTree A),
                LTree_bisimilar t1 t'1 ->
                LTree_bisimilar t2 t'2 ->
                LTree_bisimilar (LBin a t1 t2) (LBin a t'1 t'2).

Instance LTree_bisimilar_refl : Reflexive  LTree_bisimilar.
Proof.
 cofix H; intro a; case a ; constructor; auto.
Qed.

Instance LTree_bisimilar_sym : Symmetric LTree_bisimilar.
Proof.
 cofix H.
 intros x y; case x; case y.
  - left.
  -  inversion_clear 1.
  -  inversion_clear 1.
  -  inversion_clear 1;  now right. 
Qed.

Instance  LTree_bisimilar_trans : Transitive  LTree_bisimilar.
Proof.
 cofix H; intros x y z ; case x; case y.
 - inversion 2; constructor.
 - inversion 1.
 - inversion 1.
 -  inversion_clear 1.
     case z; inversion_clear 1;  right; now eapply H; eauto.
Qed.

Global Instance  bisimilar_equiv : Equivalence LTree_bisimilar.
Proof.
 split;[apply LTree_bisimilar_refl |
        apply LTree_bisimilar_sym  |
        apply LTree_bisimilar_trans].
Qed.

 Theorem LTree_bisimilar_label : 
   forall (p:path) (t t': LTree A),
          LTree_bisimilar t t' ->
          LTree_label t p = LTree_label t' p.
 Proof.
  simple induction p.
  intros t t'; case t, t'.
  - reflexivity.
  -  inversion_clear 1.
  -  inversion_clear 1.
  -  inversion_clear 1; simpl; auto.
  -  intros a l;case a; intros H t t'; case t, t'.
    + reflexivity.
    +  inversion_clear 1.
    +  inversion_clear 1.
    +  inversion_clear 1; cbn; repeat  rewrite LTree_label_rw0; auto.
    +  repeat  rewrite LTree_label_rw1; auto.
    +  inversion_clear 1.
    +  inversion_clear 1.
    +  inversion_clear 1; repeat  rewrite LTree_label_rw1; auto.
 Qed.


 Theorem label_LTree_bisimilar :  forall t t': LTree A, 
                          (forall p:path, LTree_label t p = LTree_label t' p)->
                          LTree_bisimilar t t'.
 Proof.
  cofix label_LTree_bisimilar.
  intros t t'; case t; case t'.
  - left.
  - intros a l l0 H; discriminate (H nil). 
  - intros a l l0 H; discriminate (H nil). 
  - intros a l l0 a0 t1 t2 H.
   assert (e : a = a0) by
        (generalize (H nil); injection 1; congruence).
   subst a0;  constructor;  apply label_LTree_bisimilar; intro p.
   +  generalize (H (cons d0 p));repeat rewrite LTree_label_rw0; auto.
   +  generalize (H (cons d1 p)); repeat rewrite LTree_label_rw1; auto.
 Qed.

End LTree_bisimilar_def.

