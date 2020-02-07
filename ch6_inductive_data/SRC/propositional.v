Require  Export Bool.

Inductive L : Set :=
| L_true  | L_false 
| L_disj (l1 l2 : L) | L_conj (l1 l2 : L) | L_impl (l1 l2 : L)
| L_not (l : L).


Fixpoint L_value (l : L): bool :=
 match l with
 | L_true => true
 | L_false => false
 | L_disj l1 l2 => L_value l1 || L_value l2
 | L_conj l1 l2 => L_value l1 &&  L_value l2
 | L_impl l1 l2 => implb (L_value l1) (L_value l2)
 | L_not l1 => negb (L_value l1)
 end.


(* infix notations *)

Declare Scope prop_scope.

Notation "A * B"  := (L_conj A B) : prop_scope.

Notation "A + B"  := (L_disj A B) : prop_scope.

Notation "A <= B" := (L_impl A B) : prop_scope.

Notation "'tt'" := L_true : prop_scope.

Notation "'ff'" := L_false : prop_scope.

Notation "- A" := (L_not A) : prop_scope.


Open Scope prop_scope.

(** Tests : 

Compute L_value (tt * ff).

Compute L_value (tt * ff + (tt <= ff)).

Compute L_value (- (tt * ff + (tt <= ff))).
*)

