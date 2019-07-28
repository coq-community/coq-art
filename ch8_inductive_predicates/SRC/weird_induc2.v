(* A utiliser pour prouver une propriété envoyée par pascal Molin *)




Require Import Arith.
Require Import Omega.

Section weird_induc_proof.
 Variable P : nat -> Prop.
 Variable f : nat -> nat.
 
 Hypothesis f_strict_mono : forall n p:nat, n < p -> f n < f p.
 Hypothesis f_1 : 1 < f 1.
 
 Hypothesis P0 : P 1.
 Hypothesis P_Sn_n : forall n:nat, 1<= n -> P (S n) -> P n.
 Hypothesis f_P : forall n:nat, 1<= n -> P n -> P (f n).
 
 Fixpoint iterate (A:Set) (f:A -> A) (n:nat) (x:A) {struct n} : A :=
   match n with
   | O => x
   | S p => f (iterate A f p x)
   end.




 Lemma i_f_i : forall i:nat, i <= iterate _ f i 1.
 Proof.
  induction i.

  auto with arith.
  cut (iterate _ f i 1 < iterate _ f (S i) 1).
  intros.

  clear P_Sn_n f_strict_mono f_1 f_P.
  omega.
  elim i;simpl;auto.
 Qed.

 Lemma f_le : forall i j:nat, i <= j -> 1<=i -> P j -> P i.
 Proof.
  intros i j H; elim H; auto.
  intros.
 apply H1;auto.
 apply P_Sn_n;eauto with arith.
 
 Qed.

 Lemma p_iter_f : forall i:nat, 1<= i -> P (iterate _ f i 1).
 Proof.
 induction 1;simpl;auto.
  apply f_P.
  apply le_trans with m. auto . apply i_f_i.
 auto.
 Qed.

 Theorem weird_induc : forall n:nat, 1<= n -> P n.
 Proof.
  intros n Hn.
  eapply f_le.
  eapply i_f_i.
 auto.
  apply p_iter_f.
 auto.
 Qed.

End weird_induc_proof.

Check weird_induc.
 
