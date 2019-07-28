Require Import List Extraction.
Section LLists.

Variable (A:Type).

CoInductive LList := 
  | LNil: LList
  | LCons : A -> LList -> LList.


Inductive Finite : LList -> Prop :=
  |Finite_LNil: Finite LNil
  |Finite_LCons     : forall a l, Finite l-> Finite (LCons a l).


(* An equivalent (one contructor) definition of Finite *)

Inductive Finite_alt (x:LList) :Prop := 
  |finite_alt_intro: (forall a y , x = LCons a y ->Finite_alt y)-> 
       Finite_alt x.


Lemma Finite_Finite_alt : forall x, Finite x -> Finite_alt x.
Proof.
  intros x H;induction H.
 -  constructor; intros a y H;inversion H.
 -  constructor;intros b y;injection 1; intros;subst y;assumption.
Qed.

Lemma Finite_alt_Finite : forall x, Finite_alt x -> Finite x.
Proof.
 intros x H; induction H as [x H H0]; destruct x;constructor.
 eapply H0;eauto.  
Qed.


Definition Finite_rect_0 (P:LList->Type) :
    (forall x : LList,
        (forall(h:A) (y  : LList),  x = LCons h y -> P y) -> P x) ->
    forall x : LList, Finite x -> P x.
Proof.
 intros H x Hx;apply Finite_Finite_alt in Hx.
 induction Hx.
 apply H; auto.
Defined.

Definition Finite_rect (P:LList->Type) :
 P LNil ->
 (forall x (l:LList), P l -> (P (LCons  x l))) ->
 forall l, Finite l -> P l.
Proof.
 intros X X0 l H; induction H using Finite_rect_0.
  destruct x; auto.
  apply X0; apply X1 with a;reflexivity.
Defined.



Fixpoint list_inject (l:list A) : LList :=
 match l with nil => LNil
            |List.cons a l' => LCons a (list_inject l') 
 end.

Lemma inj_Finite : forall l, Finite (list_inject l).
Proof. 
 induction l;constructor;auto.
Qed.

Definition to_list_strong: forall x, Finite x-> {l:list A | x=list_inject l}.
Proof.
  intros x H;  induction H using Finite_rect.
 -   exists nil;auto.
 -   destruct IHFinite as [l0 H0]; exists (x::l0);subst l;trivial. 
Defined.


Definition to_list: forall x, Finite x-> list A.
Proof.
  intros x Hx;destruct (to_list_strong _ Hx) as  [x0 _];  exact x0.
Defined.


End LLists.
Recursive Extraction to_list_strong.






