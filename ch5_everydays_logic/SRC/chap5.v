Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export ZArithRing.
Require Import Relations.


(** Example of use of the conversion rule 
*)
Theorem conv_example : forall n:nat, 7*5 < n -> 6*6 <= n.
Proof.
 intros; assumption.
Qed.

Theorem imp_trans : forall P Q R:Prop, (P->Q)->(Q->R)->P->R.
Proof.
  intros P Q R H H0 p.
  apply H0; apply H; assumption.
Qed.

(** Tests :

Print imp_trans.

Check (imp_trans _ _ _ (le_S 0 1)(le_S 0 2)).

*)

Definition neutral_left (A:Type)(op:A->A->A)(e:A) : Prop :=
  forall x:A, op e x = x.

Lemma one_neutral_left : neutral_left Z Zmult 1%Z.
Proof.
 intro z; ring. 
Qed.

Lemma le_i_SSi : forall i:nat, i <= S (S i).
Proof.
 intro i.
 do 2 apply le_S; apply le_n.
Qed.

Lemma all_imp_dist   : 
 forall (A:Type)(P Q:A->Prop), 
         (forall x:A, P x -> Q x)->
         (forall y:A, P y)-> 
          forall z:A, Q z.
Proof.
 intros A P Q H H0 z.
 apply H; apply H0; assumption.
Qed.


Lemma mult_le_compat_r : forall m n p:nat, le n p -> le (n * m) (p * m).
Proof.
 intros m n p H; rewrite (mult_comm n m); rewrite (mult_comm p m).
 apply mult_le_compat_l; trivial.
Qed.


Lemma le_mult_mult :
   forall a b c d:nat, a <= c -> b <= d -> a * b <= c * d.
Proof.
 intros a b c d H H0.  
 apply le_trans with (m := c  *b).
 - apply mult_le_compat_r; assumption.
 - apply mult_le_compat_l; assumption.
Qed.


(** using eapply ...
*)

Lemma le_mult_mult' : 
 forall a b c d:nat, a <= c -> b <= d -> a*b <= c*d.
Proof.
 intros a b c d H H0.  
 eapply le_trans.
 - eapply mult_le_compat_l.
   eexact H0.
 -  now apply mult_le_compat_r.
Qed.   

Lemma le_O_mult : forall n p:nat, 0 * n <= 0 * p.
Proof.
 intros n p; apply le_n.
Qed.

Lemma lt_8_9 : 8 < 9.
Proof.
 unfold lt; apply le_n.
Qed.

(** Tests :

SearchPattern (_ + _ <= _)%Z.

SearchPattern (?X1 * _ <= ?X1 * _)%Z. 

*)

Lemma lt_S : forall n p:nat, n < p -> n < S p.
Proof.
 intros n p H.
 unfold lt; apply le_S; trivial.
Qed.

Open Scope Z_scope.

Definition Zsquare_diff (x y:Z):= x * x - y * y.

Theorem unfold_example :
 forall x y:Z,
   x*x = y*y ->
   Zsquare_diff x y * Zsquare_diff (x+y)(x*y) = 0.
Proof.
 intros x y Heq.
 unfold Zsquare_diff at 1.
 rewrite Heq; ring. 
Qed.

Section ex_falso_quodlibet.
 Hypothesis ff : False.
 
 Lemma ex1 : 220 = 284.
 Proof.
   apply False_ind.
   exact ff.
 Qed.

 Lemma ex2 : 220 = 284.
 Proof.
  destruct ff.
 Qed.

End ex_falso_quodlibet.

Theorem absurd : forall P Q:Prop, P -> ~P -> Q.
Proof.
 intros P Q p H.
 elim H.
 assumption.
Qed.

Theorem double_neg_i : forall P:Prop, P->~~P.
Proof.
 intros P p H.
 apply H; assumption.
Qed.

Theorem modus_ponens :forall P Q:Prop, P->(P->Q)->Q.
Proof.
 auto.
Qed.


Theorem double_neg_i' : forall P:Prop, P -> ~ ~ P.
Proof.
 intro P; exact (modus_ponens P False).
Qed.

Theorem contrap :forall A B:Prop, (A->B) -> ~B -> ~A.
Proof.
 intros A B; unfold not.
 apply imp_trans.
Qed.  

Theorem disj4_3' : forall P Q R S:Prop, R -> P \/ Q \/ R \/ S.
Proof.
  right; right; left; assumption.
Qed.

Lemma and_commutes : forall A B:Prop, A /\ B -> B /\ A.
Proof.
 intros A B H; destruct H.
 split; assumption.
Qed.

Lemma or_commutes : forall A B:Prop, A\/B->B\/A.
Proof.
 intros A B H; destruct H as [H | H]; auto.
Qed.

Lemma ex_imp_ex :
 forall (A:Type)(P Q:A->Prop), (ex P)->(forall x:A, P x -> Q x)->(ex Q).
Proof.
 intros A P Q H H0; destruct H as [a Ha].
 exists a; apply H0; assumption.
Qed.


Lemma L36 : 6 * 6 =9 * 4.
Proof. reflexivity. Qed.

Lemma diff_of_squares : forall a b:Z, ((a + b) * (a - b) = a * a - b * b)%Z.
Proof.
 intros; ring.
Qed.

Theorem eq_sym' : forall (A:Type)(a b:A), a = b -> b = a.
Proof.
 intros A a b e; rewrite e; reflexivity.
Qed.

Lemma Zmult_distr_1 : forall n x:Z, n * x + x = ( n + 1) * x.
Proof.
 intros n x ; rewrite Zmult_plus_distr_l.
 now rewrite  Zmult_1_l.
Qed.

Lemma regroup : forall x:Z, x + x + x + x + x = 5 * x.
Proof.
 intro x; pattern x at 1.
 rewrite <- Zmult_1_l.
 repeat rewrite Zmult_distr_1.
 reflexivity.
Qed.


Open Scope nat_scope. 

Theorem le_lt_S_eq : forall n p:nat, n <= p -> p < S n -> n = p.
Proof.
 intros; omega.
Qed.

Lemma conditional_rewrite_example : forall n:nat,
   8 < n + 6 ->  3 + n < 6 -> n * n = n + n.
Proof.
 intros n  H H0.
 rewrite <- (le_lt_S_eq 2 n).
 - reflexivity.  
 -  apply  plus_le_reg_l with (p := 6). 
    rewrite plus_comm in H; auto with arith.
 - apply   plus_lt_reg_l with (p:= 3); auto with arith.
Qed.

(** A shorter proof ...
*)

Lemma conditional_rewrite_example' : forall n:nat,
   8 < n + 6 ->  3 + n < 6 -> n * n = n + n.
Proof.
 intros n  H H0.
 assert (n = 2) by omega.
 now subst n.
Qed.


Theorem eq_trans :
   forall (A:Type)(x y z:A), x = y -> y = z -> x = z. 
Proof.
 intros A x y z H; rewrite H; auto. 
Qed. 

Definition my_True : Prop 
:= forall P:Prop, P -> P.

Definition my_False : Prop
:= forall P:Prop, P.

Theorem my_I : my_True.
Proof.
 intros P p; assumption.
Qed.


Theorem my_False_ind : forall P:Prop, my_False->P.
Proof.
 intros P F; apply F.
Qed.

Definition my_not (P:Prop) : Prop := P->my_False.

Section leibniz.

 Variable A : Type.
 
 Definition leibniz (a b:A) : Prop := 
 forall P:A -> Prop, P a -> P b.


Theorem leibniz_sym : symmetric A leibniz.
Proof.
 intros x y H Q; apply H; trivial.
Qed.

End leibniz.

Definition my_and (P Q:Prop) := 
  forall R:Prop, (P->Q->R)->R.

Definition my_or (P Q:Prop) := 
  forall R:Prop, (P->R)->(Q->R)->R.

Definition my_ex (A:Type)(P:A->Prop) :=
  forall R:Prop, (forall x:A, P x -> R)->R.

Definition my_le (n p:nat) :=
  forall P:nat -> Prop, P n ->(forall q:nat, P q -> P (S q))-> P p.
