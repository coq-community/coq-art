Require Export ZArith.

Inductive Z_btree : Set :=
  Z_leaf : Z_btree | Z_bnode : Z->Z_btree->Z_btree->Z_btree.

Inductive btree (A:Type) :Type :=
  bleaf : btree A | bnode : A ->btree A->btree A->btree A.

Fixpoint Z_btree_to_btree (t:Z_btree) : btree Z :=
  match t with
    Z_leaf => bleaf Z
  | Z_bnode x t1 t2 => bnode Z x
                         (Z_btree_to_btree t1)
                         (Z_btree_to_btree t2)
  end.

Fixpoint btree_to_Z_btree (t:btree Z) : Z_btree :=
  match t with
    bleaf _ => Z_leaf
  | bnode _ x t1 t2 => Z_bnode x
                         (btree_to_Z_btree t1)
                         (btree_to_Z_btree t2)
  end.

Theorem btree_to_Z_inv :
 forall t, Z_btree_to_btree (btree_to_Z_btree t) = t.
Proof.
 intros t; elim t; simpl; auto.
 intros x t1 IHt1 t2 IHt2; rewrite IHt1; rewrite IHt2;auto.
Qed.

Theorem Z_btree_to_inv :
 forall t, btree_to_Z_btree (Z_btree_to_btree t) = t.
Proof.
 intros t; elim t; simpl; auto.
 intros x t1 IHt1 t2 IHt2; rewrite IHt1; rewrite IHt2;auto.
Qed.
