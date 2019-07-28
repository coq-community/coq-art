Section simple_proofs.
 Variables P Q R S : Prop.

 Lemma id_P : P -> P.
 Proof. auto.  Qed. 
 

 Lemma id_PP : (P -> P) -> P -> P.
 Proof. auto.  Qed. 
 
 Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
 Proof. auto. Qed.

 Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
 Proof. auto. Qed.

 Lemma ignore_Q : (P -> R) -> P -> Q -> R.
 Proof. auto. Qed.

 Lemma delta_imp : (P -> P -> Q) -> P -> Q.
 Proof. auto. Qed.

 Lemma delta_impR : (P -> Q) -> P -> P -> Q.
 Proof. auto. Qed.

 Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
 Proof. auto. Qed.


 Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
 Proof. auto.  Qed.

End simple_proofs.
