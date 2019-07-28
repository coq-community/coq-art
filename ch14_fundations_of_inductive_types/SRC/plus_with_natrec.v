
Definition direct_plus :=
  nat_rec (fun n:nat => nat -> nat) (fun p:nat => p)
    (fun (n':nat) (plus_n':nat -> nat) (p:nat) => S (plus_n' p)).

Lemma test : direct_plus 8 9 = 17.
Proof. reflexivity. Qed.


Theorem direct_plus_correct : forall n p:nat, n + p = direct_plus n p.
Proof.
 simple induction n; destruct  p; simpl in |- * ; auto.  
Qed.


