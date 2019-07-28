Section partial_functions.

 Variable P : nat -> Prop.
 Variable f : nat -> option nat.
 
 Hypothesis f_domain : forall n, P n <-> f n <> None.

 Definition g n : option nat := 
     match f (n+2) with None => None 
                      | Some y => Some (y + 2) end.


 Lemma g_domain : forall n, P (n+2) <-> g n <> None.
 Proof. 
  unfold g; intro n; case (f_domain (n+2)); intros H1 H2.
  split; intro H;  case_eq (f (n+2)) .
  -  discriminate.     
  -  intro H3; now destruct (H1 H). 
  -  intros n0 H3; apply H2; rewrite H3; discriminate.
  -  intro H3; rewrite H3 in H; now destruct H.  
Qed.

End partial_functions.
