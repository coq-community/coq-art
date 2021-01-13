Require Import List  Arith Omega.

Section mirror.

 Variable A : Type.

 Inductive remove_last (a:A) : list A -> list A -> Prop :=
   | remove_last_hd : remove_last a (a :: nil) nil
   | remove_last_tl :
       forall (b:A) (l m:list A),
         remove_last a l m -> remove_last a (b :: l) (b :: m). 

 Inductive palindrome : list A -> Prop :=
   | empty_pal : palindrome nil
   | single_pal : forall a:A, palindrome (a :: nil)
   | cons_pal :
       forall (a:A) (l m:list A),
         palindrome l -> remove_last a m l -> palindrome (a :: m).
 
 #[local] Hint Constructors remove_last palindrome : core.


 Lemma ababa : forall a b:A, palindrome (a :: b :: a :: b :: a :: nil).
 Proof.
  eauto 7.
 Qed.


(* more about palindromes *)

Lemma remove_last_inv :
 forall (a:A) (l m:list A), remove_last a m l -> m = l ++ a :: nil.
Proof.
 intros a l m H; elim H; simpl; auto with datatypes.
 intros b l0 m0 H0 e; rewrite e; trivial.
Qed.

Lemma rev_app : forall l m:list A, rev (l ++ m) = rev m ++ rev l.
Proof.
 intros l m; elim l; simpl; auto with datatypes.
 intros a l0 H0; rewrite ass_app; rewrite H0; auto.
Qed.

Lemma palindrome_rev : forall l:list A, palindrome l -> rev l = l.
Proof.
 intros l H; elim H; simpl; auto with datatypes.
 intros a l0 m H0 H1 H2; generalize H1; inversion_clear H2.
 -  simpl; auto.
 -  rewrite (remove_last_inv _ _  _ H3); simpl; repeat (rewrite rev_app; simpl).
    intro eg; rewrite eg;  simpl; auto.
Qed.

(* A new induction principle for lists *)

(* preliminaries *)

Lemma length_app :
 forall l l':list A, length (l ++ l') = length l + length l'.
Proof.
  intro l; elim l; simpl; auto.
Qed.

Lemma fib_ind :
 forall P:nat -> Prop,
   P 0 ->
   P 1 -> 
  (forall n:nat, P n -> P (S n) -> P (S (S n))) -> 
  forall n:nat, P n.
Proof.
 intros P H0 H1 HSSn n.
 assert (H2 : P n /\ P (S n)).
 - induction n ;[tauto | ].
   destruct IHn;split;auto.
 -  destruct H2; auto.
Qed.

Section Proof_of_list_new_ind.
Variables (P : list A -> Prop).

Hypotheses (H0 : P nil)
           (H1 : forall a: A, P (a::nil))
           (H2 : forall (a b:A) (l:list A), P l -> P (a :: l ++ b :: nil)).  
   
Lemma list_cut : 
forall (l:list A) (x:A),
            exists b : A, exists l' : list A, x :: l = l' ++ b :: nil.
Proof.
intro l; elim l; simpl.
 intro x; exists x; exists (nil (A:=A)); auto.
 intros a1 l3 H x.
 case (H a1).
 intros x0 H7.
 case H7; intros b Hb.
 rewrite Hb.
 exists x0.
 exists (x :: b); auto.
Qed.



Lemma list_new_ind_length :
forall (n:nat) (l:list A), length l = n -> P l.
Proof.
intro n; pattern n; apply fib_ind.
  -  intro l; case l; [simpl; auto with datatypes |  discriminate].
  -  intro l; case l; simpl; [ discriminate | ].
     +  intros a l0; case l0; simpl; [auto | discriminate].
  -  intros n0 H3 H4 l; case l; simpl;[discriminate |].
     +  intros a l0 H5; generalize H5; case l0. 
       *   simpl; discriminate 1.
       *   intros a0 l1 H6; destruct (list_cut l1 a0) as [x [l' Hx]];
           rewrite Hx; apply H2.
           apply H3.
           rewrite Hx in H6.
           rewrite length_app in H6.
           simpl in H6; omega.
Qed.


Lemma list_new_ind :
   forall l:list A, P l.
Proof.
 intro l; now apply list_new_ind_length with (length l).
Qed. 


End Proof_of_list_new_ind.



Lemma app_left_reg : forall l l1 l2:list A, l ++ l1 = l ++ l2 -> l1 = l2.
Proof.
 intro l; elim l; simpl; auto.
 intros a l0 H0 l1 l2 H; injection H; auto.
Qed.

Lemma app_right_reg : forall l l1 l2:list A, l1 ++ l = l2 ++ l -> l1 = l2.
Proof.
 intros l l1 l2 e.
 assert (H: rev (l1 ++ l) = rev (l2 ++ l)).
 - now rewrite e.
 -  repeat rewrite rev_app in H.
    generalize (app_left_reg _ _ _ H).
    intro H1;  rewrite <- (rev_involutive  l1) ; 
    rewrite <- (rev_involutive l2);
    rewrite H1; auto.
    Qed.

Theorem rev_pal : forall l:list A, rev l = l -> palindrome  l. 
Proof.
 intro l; elim l using list_new_ind; auto.
 -  intros a b l0 H H0.
    apply cons_pal with l0.
   +  apply H;  simpl in H0;  rewrite rev_app in H0.
      simpl in H0; injection H0.
      intros H1 e; generalize H1; rewrite e.
      intro H2; generalize (app_right_reg _ _ _ H2); auto.
   +  simpl in H0; rewrite rev_app in H0; simpl in H0.
      injection H0; intros H1 H2; rewrite <- H2.
      generalize l0; intro l1; induction l1; simpl; auto.
Qed.


End mirror.
