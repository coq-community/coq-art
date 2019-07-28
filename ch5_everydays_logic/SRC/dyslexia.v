Definition dyslexic_imp := forall P Q:Prop, (P -> Q) -> Q -> P.

Definition dyslexic_contrap := forall P Q:Prop, (P -> Q) -> ~ P -> ~ Q.


Section dyslexia.
 Hypothesis d : dyslexic_imp.

 Theorem incons1 : False. 
 Proof.
  now apply (d False True).
 Qed.

End dyslexia.

Section dyslexia2.
 Hypothesis s : dyslexic_contrap.

 Lemma incons2 : False.
 Proof.
  apply (s False True); [ | unfold not |];trivial.
 Qed.

End dyslexia2.
