Definition my_le (n p:nat) :=
  forall P:nat -> Prop, 
    P n -> 
    (forall q:nat, P q -> P (S q)) -> 
    P p.

Example my_le_4_7 : my_le 4 7.
Proof.
 intros P H4 HS.
 do 3 apply HS; assumption.
Qed.


Lemma my_le_n : forall n:nat, my_le n n.
Proof.
  unfold my_le; auto.
Qed.

Lemma my_le_S : forall n p:nat, my_le n p -> my_le n (S p).
Proof.
  unfold my_le; intros n p H P H0 H1.
  apply H1;  now apply H.
Qed.

(* some more proofs *)

Lemma my_le_inv : forall n p:nat, my_le n p -> n = p \/ my_le (S n) p.
Proof.
 intros n p H; apply H.
 - now  left.
 -  intros q d; case d.
   +  intro e; rewrite e; right; apply my_le_n.
   +  right; apply my_le_S; assumption.
Qed.
 
Lemma my_le_inv2 :
 forall n p:nat, my_le (S n) p ->  exists q : nat, p = S q /\ my_le n q.
Proof.
 intros n p H; apply H.
 -  exists n; split.
   + reflexivity.  
   +  apply my_le_n.
 -  intros q Hq; case Hq; intros q0 [H0 H1].
    exists q; split.
   + reflexivity. 
   +  rewrite H0; now apply my_le_S.
Qed.

Lemma my_le_n_O : forall n:nat, my_le n 0 -> n = 0.
Proof.
 intros n; case n.
 - reflexivity. 
 - intros n0 H0; case (my_le_inv2 _ _ H0).
   intros x [e H]; discriminate e.
Qed.


Lemma my_le_le : forall n p:nat, my_le n p -> n <= p. 
Proof.
 intros n p H;apply H;auto.
Qed.


Lemma le_my_le : forall n p:nat, n <= p -> my_le n p. 
Proof.
 induction 1.
 - apply my_le_n.
 - apply my_le_S; assumption.
Qed.

