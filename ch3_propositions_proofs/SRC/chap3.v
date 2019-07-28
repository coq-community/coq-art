
Section Minimal_propositional_logic.
 Variables P Q R T : Prop.


 Theorem imp_trans : (P->Q)->(Q->R)->P->R.
 Proof.
  intros H H' p.
  apply H'.
  apply H.
  assumption.
 Qed.

 
 Theorem imp_trans' : (P->Q)->(Q->R)->P->R.
 Proof.
  intros H H' p; apply H'; apply H; assumption.
 Qed.

 Theorem imp_trans'' : (P->Q)->(Q->R)->P->R.
 Proof.
  auto. 
 Qed.

 Theorem delta : (P->P->Q)->P->Q.
 Proof (fun (H:P->P->Q)(p:P) => H p p).

 Lemma apply_example : (Q->R->T)->(P->Q)->P->R->T.
 Proof.
  intros H H0 p.
  apply H.
  exact (H0 p).
 Qed.

 Theorem imp_dist : (P->Q->R)->(P->Q)->(P->R).
 Proof.
  intros H H' p.
  apply H.  
  - assumption.
  - apply H'; assumption.
 Qed.

 Theorem K : P->Q->P.
 Proof.
  intros p q;  assumption.
 Qed.


 
 Section proof_of_triple_impl.
  Hypothesis H : ((P->Q)->Q)-> Q.
  Hypothesis p : P.

  Remark  R1 : (P->Q)->Q.
  Proof fun H0:P->Q => H0 p.

  Theorem triple_impl : Q.
  Proof H R1.

 End proof_of_triple_impl.


 Theorem triple_impl_one_liner : (((P->Q)->Q)->Q)->P->Q.
 Proof.
  intros H p; apply H; intro H0; apply H0; assumption.
 Qed.

 Lemma imp_dist' : (P->Q->R)->(P->Q)->(P->R).
 Proof.
  intros H H' p.
  apply H;[assumption | apply H'; assumption].
 Qed.





 Section section_assert_example.
  Hypotheses (H : P->Q)
             (H0 : Q->R)
             (H1 : (P->R)->T->Q)
             (H2 : (P->R)->T).
 
  Lemma assert_example : Q.
  Proof.
   assert (H3 : P -> R).
   -  intro p; apply H0; apply H; assumption.
   -  apply H1;[assumption | apply H2; assumption].
  Qed.

 Print assert_example.

 End section_assert_example.

 Lemma triple_impl2 : (((P->Q)->Q)->Q)->P->Q.
 Proof.
  auto.
 Qed.

End Minimal_propositional_logic.

Print imp_dist.

Section using_imp_dist.
 Variables (P1 P2 P3 : Prop).

 Check imp_dist P1 P2 P3.

 Check imp_dist (P1->P2) (P2->P3) (P3->P1).

End using_imp_dist.


