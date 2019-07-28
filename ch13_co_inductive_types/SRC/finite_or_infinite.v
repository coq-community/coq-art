Require Import chap13  Classical.

Lemma Not_Infinite_Finite {A:Type}:
  forall  l:LList A,
   ~ Infinite l -> Finite l.
Proof.
  intros l H; case (classic (Finite l)).
  -  trivial.
  - intro H0; destruct H; now apply Not_Finite_Infinite.
Qed.

Lemma Finite_or_Infinite {A: Type}:
  forall l:LList A, Finite l \/ Infinite l. 
Proof.
  intros l; case (classic (Finite l)).
  - now left. 
  - right; now apply Not_Finite_Infinite.
Qed.

