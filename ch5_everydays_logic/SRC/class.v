
Definition peirce := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~~P -> P.
Definition excluded_middle := forall P:Prop, P\/~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q)->(~P\/Q).


Lemma excluded_middle_peirce : excluded_middle -> peirce.
Proof.
 unfold peirce; intros H P Q H0.
 destruct (H P) as [p | np].
 -  assumption.
 -  apply H0; intro H1; now absurd P.
Qed.

Lemma peirce_classic : peirce -> classic.
Proof.
 intros HPeirce P H0; apply (HPeirce P False).
 intro H1; now destruct H0.
Qed.

Lemma classic_excluded_middle: classic -> excluded_middle.
Proof.
 unfold excluded_middle; intros H P.
 apply H; intro H0; absurd P.
 -  intro H1; apply H0 ; now left.
 -  apply H; intro H1; apply H0; now right.
Qed.


Lemma excluded_middle_implies_to_or :  excluded_middle -> implies_to_or.
Proof.
 intros H P Q H0;
  destruct (H P) as [p | np].
  -  right; auto.
  - now  left.
Qed.

Lemma implies_to_or_excluded_middle : implies_to_or -> excluded_middle.
Proof.
 unfold excluded_middle; intros H P; destruct (H P P);auto.
Qed.

Lemma classic_de_morgan_not_and_not : classic -> 
                                      de_morgan_not_and_not.
Proof.
 unfold de_morgan_not_and_not; intros H P Q H0.
 apply H.
 intro H1; apply H0; split;intro;apply H1; auto.
Qed.

Lemma de_morgan_not_and_not_excluded_middle : de_morgan_not_and_not ->
                                              excluded_middle.
Proof.
 unfold excluded_middle; intros H P.
 apply H; intros [H1 H2]; contradiction. 
Qed.

