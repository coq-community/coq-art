(** For eliminating  Logic.iff with rewrite *)
Require Import Setoid.

Inductive le_diff (n m:nat) : Prop :=
    le_d : forall x:nat, x + n = m -> le_diff n m.


Definition le_diff' (n m:nat) :=  exists x : _, x + n = m.


Lemma diff_diff' : forall n m:nat, le_diff n m <-> le_diff' n m.
Proof.
 intros n m ; split;
  destruct 1 as [x Hx]; now exists x.
Qed.

Theorem le_le_diff : forall n m:nat, n <= m -> le_diff n m.
Proof.
 intros n m H; induction  H as [ | m Hm [x Hx]].
 - now  exists 0. 
 -  rewrite <- Hx; now exists (S x).
Qed.

Theorem le_diff_le : forall n m:nat, le_diff n m -> n <= m.
Proof.
 intros n m [x]. generalize H. clear H.
 generalize  m.   clear m. induction x as [ | y Hy].
 - intros m e ; rewrite <-  e; constructor.
 -  intros   m e.  subst m; simpl; auto.
Qed.


Theorem le_le_diff' : forall n m:nat, n <= m -> le_diff' n m.
Proof.
 intros n m H; rewrite <- diff_diff';
  now apply le_le_diff.
Qed.

Theorem le_diff'_le : forall n m:nat, le_diff' n m -> n <= m.
Proof.
 intros n m H; rewrite <- diff_diff' in H;
  now apply le_diff_le.
Qed.

