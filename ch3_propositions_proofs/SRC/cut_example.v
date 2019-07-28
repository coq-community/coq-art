
Section cutex.
 Variables P Q R T : Prop.
 Hypothesis H : P -> Q.
 Hypothesis H0 : Q -> R. 
 Hypothesis H1 : (P -> R) -> T -> Q.
 Hypothesis H2 : (P -> R) -> T.


 Lemma Q0 : Q.
 Proof.
  apply H1.
  -  intro p; apply H0; apply H; assumption.
  -  apply H2.
    +  intro p; apply H0; apply H; assumption.
 Qed.  

 Lemma Q1 : Q.
 Proof.
  cut (P -> R).
  - intro H3.
    cut T.
    +  intro H4;  apply H1; assumption.
    +   apply H2; assumption.
  -  intro; apply H0; apply H; assumption.
 Qed.

 Lemma Q2 : Q.
 Proof.
  assert (H3 : P -> R).
  - intro; apply H0; apply H; assumption.   
  - assert (H4 : T).
    + apply H2; assumption.
    +  apply H1; assumption.
 Qed.


 Lemma Q3 : Q.
 Proof.   auto.  Qed.

(** Looking at the proof terms ...

 Print Q0.
 
 Print Q1.

 Print Q2.

 Print Q3.
*)

End cutex.
