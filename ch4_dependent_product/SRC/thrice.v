
Definition compose {A:Type} (g f:A -> A) (x:A) := g (f x).

Definition thrice {A:Type} (f:A -> A) := compose  f (compose f f).

Definition iterate_27 {A:Type} := thrice (thrice (A:=A)) .

Definition plus_27 : nat -> nat := iterate_27 S.

Require Import ZArith.

Definition mult_27 (x:Z) := iterate_27 (Zplus x) 0%Z.

Definition exp_27 (x:Z) := iterate_27 (Zmult x) 1%Z.


(** Tests :

Compute plus_27 0.

Compute mult_27 10. 

Compute exp_27 2.

*)
