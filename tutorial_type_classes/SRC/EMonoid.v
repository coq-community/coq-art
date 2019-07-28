(** Monoid over a setoid *)

Set Implicit Arguments.
Require Import Morphisms Relations.


Class EMonoid (A:Type)(E_eq :relation  A)(dot : A->A->A)(one : A):={
  E_rel :> Equivalence E_eq; 
  E_dot_proper :> Proper (E_eq ==> E_eq ==> E_eq) dot; 
  E_dot_assoc : forall x y z:A, E_eq (dot x (dot y z)) (dot (dot x y) z);
  E_one_left : forall x, E_eq (dot one  x) x;
  E_one_right : forall x, E_eq (dot x  one) x}.

Generalizable Variables A E_eq dot one.


Fixpoint Epower `{M: EMonoid }(a:A)(n:nat) :=
  match n with 0%nat => one
             | S p => dot a (Epower a p)
  end.

Class Abelian_EMonoid `(M:EMonoid ):= {
  Edot_comm : forall x y, E_eq (dot x  y)  (dot y  x)}.




