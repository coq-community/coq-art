Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Require Export Recdef.
 
Fixpoint exp2 (n : nat) : nat :=
 match n with 0 => 1 | S p => 2 * exp2 p end.

Lemma exp2_positive : forall n, exp2 n <> 0.
Proof. 
 induction n as [ | n IHn].
 - discriminate.  
 - simpl;  destruct (exp2 n).
   + now destruct IHn.   
   + discriminate.
Qed.


Fixpoint div2 (n:nat) : nat :=
match n with 0 | 1 => 0
            | S (S p) => S (div2 p)
end.

Lemma div2_double : forall n, div2 (2 * n) = n.
Proof.   
  induction n as [ | n IHn].
 -   simpl;auto.
 -  replace (2 * S n) with (S (S (2 * n))) by omega.
    simpl in *; now rewrite IHn.
Qed.

Theorem div2_rect :
  forall (P : nat ->  Type),
    P 0 -> P 1 -> (forall n, P n ->  P (S (S n))) -> forall (n : nat),  P n.
Proof.
  intros P H0 H1 Hrec n; assert (P n * P (S n))%type.
  - elim n; intuition.
  - intuition.
Qed.



Lemma div2_le : forall n,  div2 n <= n.
Proof.
  induction n using  div2_rect; auto.
  - simpl;auto with arith.
Qed.

Lemma div2_lt : forall n,  n <> 0 -> div2 n < n.
Proof.
  induction n as [| | n IHn] using div2_rect; auto.
  - now destruct 1.
  - simpl;intros.
    apply le_lt_trans with (S n);auto.
    generalize (div2_le n);auto with arith.
Qed.

 
Function log2 (n:nat) {measure (fun n:nat => n)} :=
match n with 0 | 1 => 0
           | n => S (log2 (div2 n))
end.
 intros; apply div2_lt; discriminate.
Qed.



(** Tests :

About log2_rect.
*)

Lemma log_of_exp2_0  : forall n p, n = exp2 p -> log2  n = p. 
Proof.
 intro n; functional induction (log2 n).
 - induction p;simpl; try discriminate.
   intro H; case_eq (exp2 p).
     intro H0;  destruct (exp2_positive p);auto.      
     intros n H0;rewrite H0 in H;discriminate.
 -  destruct p.
    + auto.
    + simpl.
      intro H.
      case_eq (exp2 p).
      * intro H0; destruct (exp2_positive p);auto.
      * intros n H0;  rewrite H0 in H; elimtype False; omega.   
 - intros p H;  destruct p. 
   +  simpl in H;  subst n;    contradiction. 
   +  simpl in H; rewrite (IHn0 p); auto. 
    rewrite H;   generalize (div2_double (exp2 p));auto.
Qed.

Lemma log_of_exp2 : forall n:nat, log2 (exp2 n) = n.
Proof.
 intro n; now apply log_of_exp2_0.
Qed.

