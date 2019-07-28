(** Binary trees the nodes of which are labelled with type A *)

Require Import Omega
        Inverse_Image Wellfounded.Inclusion Wf_nat.

Section Some_type_A.
Variable A: Type.

Inductive tree  : Type :=
  | leaf  
  | node (label: A)(left_son right_son : tree).


Inductive subtree  (t:tree) : tree -> Prop :=
  | subtree1 : forall t'  (x:A), subtree  t (node  x t t')
  | subtree2 : forall (t':tree) (x:A), subtree  t (node  x t' t).

Theorem well_founded_subtree :  well_founded subtree.
Proof.
 intros t; induction  t as [ | x t1 IHt1 t2 IHt2].
 - split; inversion 1. 
 - split; intros y Hsub; inversion_clear Hsub; assumption.
Qed.

(** Alternate arithmetic proof 

   Using several lemmas in library Wellfounded, we use tree size
  as a measure for proving well_foundedness 

*)



Fixpoint size (t:tree) : nat :=
match t with leaf => 1
           | node _ t1 t2 => 1 + size t1 + size t2
end.



Lemma subtree_smaller : forall (t t': tree), subtree t t' -> size t < size t'.
Proof. 
 inversion 1;simpl;omega.
Qed.

Lemma well_founded_subtree' : well_founded subtree.
Proof.
 apply wf_incl with (fun t t' => size t < size t').
 intros x y Hxy; now  apply subtree_smaller.
 apply wf_inverse_image; apply lt_wf.
Qed.

End Some_type_A.