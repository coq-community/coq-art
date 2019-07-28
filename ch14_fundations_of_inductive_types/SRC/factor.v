Require Import List.
Set Implicit Arguments.

Section A_fixed.

Variable A: Type. 

Inductive lfactor  : list A -> list A -> Prop :=
  | lf1 : forall u:list A, lfactor nil u
  | lf2 : forall (a:A) (u v:list A), lfactor u v ->
                                     lfactor (a :: u) (a :: v).

 Lemma lfactor_inv_head : forall a b  u v, lfactor (a::u) (b::v) ->
                                           a = b.
 Proof.
   now inversion_clear 1.
 Qed.

Definition lfactor_suffix :
  forall  u v:list A, lfactor u v -> {w : list A | v = u ++ w}.
 intros  u; induction  u as [| a u IHu].
 - intros v; now exists v.
 - intro v; case v.
    + intros Hf; exfalso; inversion_clear Hf.
    + intros b v' Hv';  generalize (lfactor_inv_head Hv'); intro;subst b.
      destruct (IHu v') as [w Hw].
      * now  inversion_clear Hv'.
      * exists w; rewrite Hw;auto.
Defined.


End A_fixed.

  