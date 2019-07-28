Require Import Arith.

Fixpoint plus'' (n m:nat) {struct m} : nat :=
  match m with
    | 0 =>  n 
    | S p => plus'' (S n) p 
  end.

Lemma plus''_S : forall p n:nat, plus'' (S n) p = S (plus'' n p).
Proof.
 simple induction p ;  simpl; auto.
Qed.

Lemma plus''_assoc : forall n p q, plus'' n (plus'' p q) =
                                   plus'' (plus'' n p) q.
Proof.
 simple induction q.
 -  reflexivity. 
 -  simpl.
    intros; rewrite plus''_S.
    simpl; repeat  rewrite plus''_S; auto.
Qed.
