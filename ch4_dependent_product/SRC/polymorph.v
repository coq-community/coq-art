Check (forall A:Type, A -> A).

Definition id (A:Type) (a:A) : A := a.

Check (forall A B:Type, (A -> A -> B) -> A -> B).

Definition diag (A B:Type) (f:A -> A -> B) (a:A) : B := f a a.


Check (forall A B C:Type, (A -> B -> C) -> B -> A -> C).
 
Definition permute (A B C:Type) (f:A -> B -> C) (b:B) (a:A) : C := f a b.

Require Import ZArith.

Check (forall A:Type, (nat -> A) -> Z -> A).

Definition f_nat_Z (A:Type) (f:nat -> A) (z:Z) : A := f (Z.abs_nat z).
