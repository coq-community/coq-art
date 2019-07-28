Require Import Arith Omega.

Definition divides (n m:nat) := exists p:nat, p*n = m.


Lemma divides_O : forall n:nat, divides n 0.
Proof.
  intro n; exists 0; simpl; trivial.
Qed.

Lemma divides_plus : forall n m:nat, divides n m -> divides n (n+m).
Proof.
 intros n m H; elim H; intros q Hq.  
 exists (S q) ; simpl; auto.
Qed.

Lemma not_divides_plus : forall n m:nat, ~ divides n m -> ~ divides n (n+m).
Proof.
 intros n m H; red; intro H'; elim H'; intro y.
 case y; simpl.
 intro H2; apply H.
 cut (m=0).
 intro H3; rewrite H3; apply divides_O.
 Require Omega.
 omega.
 intros n0 Hn0.
 apply H.
 exists n0.
 omega.
Qed.

Lemma not_divides_lt : forall n m:nat, 0<m ->  m<n -> ~ divides n m.
Proof.
 intros n m H H0 H1.
 elim H1; intros q Hq.
 rewrite <- Hq in H.
 rewrite <- Hq in H0.
 generalize H H0; case q.
 simpl.  
 intros; absurd (0 < 0); auto with arith.
 clear H H0; intros y Hy Hy'.
 simpl in Hy'. 
 absurd (n <= n + y * n); auto with arith. 
Qed.

Lemma not_lt_2_divides : forall n m:nat, n <> 1 -> n < 2 -> 0 < m -> 
                        ~ divides n m.
Proof.
 intros n m H H0; cut (n=0).
 intro e;rewrite e.   
 case m.
 intro; absurd (0 < 0); auto with arith.
 intros n0 Hn0 H1.
 elim H1; intros q Hq.
 rewrite mult_0_r in Hq; discriminate Hq.
Require Import Omega.  
 omega.
Qed.
  
Lemma le_plus_minus : forall n m:nat, le n m -> m = n+(m-n).
Proof.
 intros; omega.
Qed.

Lemma lt_lt_or_eq : forall n m:nat, n < S m ->  n<m \/  n=m.
Proof.
 intros; omega. 
Qed.
