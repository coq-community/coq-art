Require Import Relations.
Section Sequences.
 Variable A : Type.

 Variable R : A -> A -> Prop. 

 Lemma not_acc : forall a b:A, R a b -> ~ Acc R a -> ~ Acc R b.
 Proof.
  intros a b H H0 H1;  absurd (Acc R a); auto.
  generalize a H; now induction H1.
 Qed.

 Lemma acc_imp : forall a b:A, R a b -> Acc R b -> Acc R a.
 Proof.
  intros a b H H0;  generalize a H; now induction H0.
 Qed.

 Hypothesis W : well_founded R.
 #[local] Hint Resolve W : core.
	
 Section seq_intro.
  Variable seq : nat -> A. 

  Let is_in_seq (x:A) :=  exists i : nat, x = seq i.

  Lemma not_decreasing_aux : ~ (forall n:nat, R (seq (S n)) (seq n)). 
  Proof.
   unfold not in |- *; intro Hseq.
  assert  (H : forall a:A, is_in_seq a -> ~ Acc R a).
  -   intro a; pattern a in |- *; apply well_founded_ind with A R; auto.
      intros x Hx [i Hi]; generalize (Hseq i); intro H0; rewrite Hi.
      apply not_acc with (seq (S i)); auto.
      apply Hx.
      +  rewrite Hi; auto.
      +  exists (S i); auto.
  - apply (H (seq 0)). 
    +  exists 0; trivial. 
    + apply W.
 Qed.


 End seq_intro.

 Theorem not_decreasing :
  ~ (exists seq : nat -> A, (forall i:nat, R (seq (S i)) (seq i))).
 Proof.
   intros [s Hs];  now apply (not_decreasing_aux s).
 Qed.

End Sequences.

