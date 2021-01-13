
Set Implicit Arguments.

CoInductive LList (A:Type) : Type :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Arguments LNil {A}.

CoInductive Infinite {A:Type} : LList A -> Prop :=
    Infinite_LCons :
      forall (a:A) (l:LList A), Infinite l -> Infinite (LCons a l).

#[export] Hint Constructors Infinite : core.

 

Definition Infinite_ok {A:Type} (X:LList A -> Prop) : Prop :=
  forall l:LList A,
    X l ->  exists a : A, exists l' : LList A, l = LCons a l' /\ X l'.

Definition Infinite_alt {A:Type} (l:LList A) :=
   exists X : LList A -> Prop, Infinite_ok X /\ X l.


