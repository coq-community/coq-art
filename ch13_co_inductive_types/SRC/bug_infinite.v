(** Buggy definition of Infinity *)


CoInductive LList (A:Type) : Type :=
  | LNil : LList A
  | LCons : A -> LList A -> LList A.

Arguments LNil {A}.
Arguments LCons {A} _ _.

Inductive BugInfinite {A: Type} : LList A -> Prop :=
    BugInfinite_intro :
      forall a (l:LList A),
        BugInfinite l -> BugInfinite (LCons a l).

Theorem Buginfinite_is_empty {A: Type}:
  forall (l:LList A), BugInfinite l -> False.
Proof.   induction 1; assumption.
Qed.


