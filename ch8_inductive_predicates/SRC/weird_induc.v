Require Import Arith.
Require Import Omega.

Section weird_induc_proof.
 Variable P : nat -> Prop.
 Variable f : nat -> nat.
 
 Hypothesis f_strict_mono : forall n p:nat, n < p -> f n < f p.
 Hypothesis f_O : 0 < f 0.
 
 Hypothesis P0 : P 0.
 Hypothesis P_Sn_n : forall n:nat, P (S n) -> P n.
 Hypothesis f_P : forall n:nat, P n -> P (f n).
 
 Fixpoint iterate {A:Type} (f:A -> A) (n:nat) (x:A) {struct n} : A :=
   match n with
   | O => x
   | S p => f (iterate  f p x)
   end.


 Lemma i_f_i : forall i:nat, i <= iterate  f i 0.
 Proof.
 induction i as [ | n IHn].
 -   auto with arith.
 - assert (H0: iterate  f n 0 < iterate  f (S n) 0).
   +  clear  IHn; induction n;simpl;auto.
   +  omega.
 Qed.

 Lemma f_le : forall i j:nat, i <= j -> P j -> P i.
 Proof.
  intros i j H; induction H; auto.
 Qed.

 Lemma p_iter_f : forall i:nat, P (iterate  f i 0).
 Proof.
  induction i; simpl; auto.
 Qed.

 Theorem weird_induc : forall n:nat, P n.
 Proof.
  intro n;  apply (f_le n (iterate  f n 0)).
  apply i_f_i.
  apply p_iter_f.
 Qed.

End weird_induc_proof.

(**

Check weird_induc.
 
*)