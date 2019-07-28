(**

Check le_ind.

*)


Theorem lt_le : forall n p:nat, n < p -> n <= p.
Proof.
 intros n p H; pattern p. 
 apply le_ind with (n := (S n)).
 -  repeat constructor.
 -  intros; repeat constructor ; assumption. 
 - assumption. 
Qed.

