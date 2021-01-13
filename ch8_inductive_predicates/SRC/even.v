Require Import Arith.

Inductive even : nat -> Prop :=
  | O_even : even 0
  | plus_2_even : forall n:nat, even n -> even (S (S n)).


#[export] Hint Constructors even : core.

Fixpoint mult2 (n:nat) : nat :=
  match n with
  | O => 0
  | S p => S (S (mult2 p))
  end.

Lemma mult2_even : forall n:nat, even (mult2 n).
Proof. 
 induction n; simpl; auto.
Qed.

Theorem sum_even : forall n p:nat, even n -> even p -> even (n + p).
Proof.
 intros n p Heven_n; induction  Heven_n; simpl; auto.
Qed.

#[export] Hint Resolve sum_even : core.

Lemma square_even : forall n:nat, even n -> even (n * n).
Proof.
 intros n Hn; elim Hn; simpl; auto.
 intros n0 H0 H1; rewrite (mult_comm n0 (S (S n0))).
 right; simpl;apply sum_even; auto.
Qed.


Lemma even_mult2 : forall n:nat, even n -> (exists p, n = mult2 p).
Proof.
 induction 1.
 -  exists 0; reflexivity.
 -  destruct IHeven as [p Hp]; exists (S p); simpl; now rewrite Hp. 
Qed.

