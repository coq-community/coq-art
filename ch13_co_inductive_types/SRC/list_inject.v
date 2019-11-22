Set Implicit Arguments.

Require Import List  Image.

CoInductive LList (A:Type) : Type :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Arguments LNil {A}.

Fixpoint llist_injection {A:Type} (l:list A) :  LList A :=
  match l with
  | nil => LNil
  | a :: l' => LCons a (llist_injection l')
  end.

Theorem llist_injection_inj {A:Type}:
  injective _ _ (llist_injection (A:=A)).
Proof.
 unfold injective in |- *.
 -  simple induction x; simpl in |- *.
    simple destruct y; simpl in |- *; [ auto | discriminate 1 ].
    intros a l Hl y; case y; simpl in |- *.
   +  discriminate 1.
   +  injection 1; intros e1 e2; rewrite e2; rewrite (Hl _ e1); trivial.
Qed.
