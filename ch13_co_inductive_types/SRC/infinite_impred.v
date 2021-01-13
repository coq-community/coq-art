Set Implicit Arguments.


CoInductive LList (A:Type) : Type :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Arguments LNil {A}.

CoInductive Infinite {A:Type} : LList A -> Prop :=
    Infinite_LCons :
      forall (a:A) (l:LList A), Infinite l -> Infinite (LCons a l).

#[export] Hint Constructors Infinite: llists.

  

Definition Infinite_ok {A: Type} (X:LList A -> Prop) : Prop :=
  forall l:LList A,
    X l ->  exists a : A, exists l' : LList A, l = LCons a l' /\ X l'.
 
Definition Infinite1 {A: Type} (l:LList A) :=
   exists X : LList A -> Prop, Infinite_ok X /\ X l.


Lemma ok_LNil {A: Type}:
 forall X:LList A -> Prop, Infinite_ok X -> ~ X LNil.
Proof.
 unfold Infinite_ok.
 intros X H H0;  case (H LNil).  
 - assumption. 
 - intros x H1; case H1; intros x0 H2; case H2; discriminate 1.
Qed.

Lemma ok_LCons {A: Type} :
  forall  (X:LList A -> Prop) (a:A) (l:LList A),
   Infinite_ok X -> X (LCons a l) -> X l.
Proof.
 intros  X a l H H0; case (H (LCons a l)).
 -  assumption.
 -  simple destruct 1; intros x0 H2; case H2; injection 1.
    simple destruct 1; auto.
Qed.



Lemma Infinite1_LNil {A: Type} :  ~ Infinite1 (LNil (A:=A)).
Proof.
 intros  H; destruct H as [X [H1 H2]].
 now apply (ok_LNil H1).
Qed.


Lemma Infinite1_LCons  {A: Type} :
 forall  (a:A) (l:LList A), Infinite1 (LCons a l) -> Infinite1 l.
Proof.
 intros  a l H.
 case H; intros X HX; case HX; intros H1 H2; clear HX.
  exists (fun u:LList A =>  exists b : A, X (LCons b u)); split.
 -  unfold Infinite_ok in |- *.
    intros l0 [b Hb]. 
    assert (H4 : X l0) by apply (ok_LCons _ _  H1 Hb);eauto.  
    case (H1 l0 H4);  intros x [l' [el' Hl']].
    exists x, l'; split; try assumption.
    exists x; rewrite <- el'; auto.
-  exists a; auto.
Qed.


(* equivalence between both definitions of infinity *)


Lemma Inf_Inf1 {A : Type} : forall l:LList A, Infinite l -> Infinite1 l.
Proof.
 intros l ;  exists (Infinite (A:=A)).
 split; try assumption.
 unfold Infinite_ok in |- *.
 simple destruct l0.
 -  inversion 1.
 - inversion_clear 1.
   exists a; exists l1; auto.
Qed.

Lemma Inf1_Inf {A : Type}: forall l:LList A, Infinite1 l -> Infinite l.
Proof.
 cofix Inf1_Inf.
 simple destruct l.
 - intro H;  case (Infinite1_LNil H).
 -  intros a l0 H0;  generalize (Infinite1_LCons H0); constructor.
    now apply Inf1_Inf. 
Qed.

