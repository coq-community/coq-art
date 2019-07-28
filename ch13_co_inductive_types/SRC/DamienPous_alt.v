Set Implicit Arguments.
Require Import Eqdep Eqdep_dec  EqdepFacts.

Section s.
Variable (A:Type).

Hypothesis A_eq_dec : forall a b:A, {a=b}+{a<>b}.

CoInductive LList :=
 | LNil: LList
 | LCons : A -> LList -> LList.


Inductive Finite : LList -> Prop :=
 |Finite_LNil: Finite LNil
 |Finite_LCons   : forall a l, Finite l -> Finite (LCons a l).


(* An equivalent (one contructor) definition of Finite *)

Inductive Finite_alt (x:LList) :Prop := 
  |finite_alt_intro: (forall a y , x = LCons a y -> Finite_alt y)-> 
       Finite_alt x.

Lemma Finite_Finite_alt : forall x, Finite x -> Finite_alt x.
Proof.
  intros x H;induction H.
  -  constructor; intros a y H;inversion H.
  -  constructor;intros b y;injection 1. intros;subst y;assumption.
Qed.

Lemma Finite_alt_Finite : forall x, Finite_alt x -> Finite x.
Proof.
 intros x H; induction H as [x H H0]; destruct x;constructor.
 eapply H0;eauto.  
Qed.


Definition Finite_rect_0 (P:LList->Type) :
    (forall x : LList,
        (forall(h:A) (y  : LList),  Finite y -> x = LCons h y -> P y) -> P x) ->
    forall x : LList, Finite x -> P x.
Proof.
 intros H x Hx;apply Finite_Finite_alt in Hx.
 induction Hx.
 -  apply H; auto.
    intros; eapply X;eauto.
Defined.

Definition Finite_rect (P:LList->Type) :
  P LNil ->
  (forall x (l:LList), Finite l -> P l -> (P (LCons  x l))) ->
  forall l, Finite l -> P l.
Proof.
  intros H0 Hcons l H.
  generalize H;  elim H using Finite_rect_0.
  destruct x; auto.
  intros X H1; apply Hcons. 
  - now inversion H1.
  -  apply X with a.
   +  inversion H1;auto. 
   +  reflexivity.
   +  inversion H1;auto. 
Defined.



Notation "H == K" := (eq_dep _ Finite _ H _ K) (at level 80).

Fixpoint dep h (H: Finite h): forall k (K: Finite k), h = k -> H == K.
  destruct H; destruct K.
 -  reflexivity.
 -  discriminate.
 -  discriminate.
 -  injection 1; intros; subst a0 l0. 
    now  rewrite (dep _ H _ K ). 
Defined.

Goal forall l (H K:Finite l), H == K.
Proof.
  intros; now apply dep. 
Qed.

Lemma  LList_dec: forall h :LList,
                    Finite h ->
                    forall k, Finite k -> {h=k}+{h<>k}.
Proof.
 intros h H;elim H using Finite_rect.
 -  intros k K ; elim K using Finite_rect.
   +  left;auto.
   +  right;discriminate. 
 -  intros x l H0 H1 k K ; elim K using Finite_rect.
   +   right;discriminate. 
   + intros x0 l0 H2 H3.
     destruct (H1 _ H2).
   *  destruct (A_eq_dec x x0).
      subst x0 l; now left.
      right;intro H4;injection H4.
      intros;now destruct n.
   *  right;intro H4;injection H4; intros;destruct n;auto.
Qed.
 



Goal forall l, Finite l -> forall (H K:Finite l), H=K.
Proof.
  intros l Hl H K;  apply eq_dep_eq. (* uses an axiom ! *)
  now  apply dep. 
Qed.

End s.












