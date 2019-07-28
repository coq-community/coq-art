(* prelude : add some result to the module Rstar *)

Require Import Relations List.
Require Import Operators_Properties.
Import Relations.


Section perms.
Variable A : Type.

 Inductive transpose : list A -> list A -> Prop :=
   | transpose_hd :
       forall (a b:A) (l:list A), transpose (a :: b :: l) (b :: a :: l)
   | transpose_tl :
       forall (a:A) (l l':list A),
         transpose l l' -> transpose (a :: l) (a :: l')
  .

Definition perm := clos_refl_trans _ transpose.

Lemma transpose_sym : forall l l':list A, transpose l l' -> transpose l' l.
Proof.
 intros l l' H; elim H; [ left | right; auto ].
Qed.

Theorem equivalence_perm : equivalence _ perm.
Proof.
split.
- intro x;constructor 2.
- intros x y z;constructor 3 with y;auto.
- intros x y H; induction H.
 +  constructor 1;apply transpose_sym;assumption.
 +  constructor 2.
 +  constructor 3 with y;auto.
Qed.

End perms.
