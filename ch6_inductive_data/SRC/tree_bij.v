Require Import ZArith.
Open Scope Z_scope.


Inductive Z_btree : Set :=
  Z_leaf : Z_btree | 
  Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.


Inductive Z_fbtree : Set :=
 | Z_fleaf : Z_fbtree 
 | Z_fnode : Z  -> (bool -> Z_fbtree) -> Z_fbtree.


Definition Zf_mknode (z : Z) (t1 t2 : Z_fbtree) : Z_fbtree :=
   Z_fnode z (fun b => if b then t1 else t2).

Definition fleft_son  (t:Z_fbtree) : Z_fbtree :=
 match t with 
 | Z_fleaf => Z_fleaf
 | Z_fnode a f => f true
 end.

Definition fright_son  (t:Z_fbtree) : Z_fbtree :=
 match t with 
 | Z_fleaf => Z_fleaf
 | Z_fnode a f => f false
 end.

Fixpoint f1 (t:Z_btree) : Z_fbtree :=
  match t with
  | Z_leaf => Z_fleaf
  | Z_bnode z t1 t2 => Zf_mknode z (f1 t1) (f1 t2)
  end.


Fixpoint f2 (t:Z_fbtree) : Z_btree :=
  match t with
  | Z_fleaf => Z_leaf
  | Z_fnode z f => Z_bnode z (f2 (f true)) (f2 (f false))
  end.


Theorem f2_f1 : forall t: Z_btree, f2 (f1 t) = t.
Proof.
 induction t; simpl; auto.
 rewrite IHt1; rewrite IHt2; trivial.
Qed.

Section Extensionnality.
 Hypothesis extensionality : forall (A B:Type) (f g: A -> B),
                             (forall a, f a = g a)-> f =g.

 Theorem f1_f2 :  forall t: Z_fbtree, f1 (f2 t) = t.
 Proof.
  induction t; simpl; auto.
  -  do 2 rewrite H.
     unfold Zf_mknode.
     rewrite <- (extensionality _ _ 
                (fun b:bool =>  if b then z0 true else z0 false)
                z0). 
     + trivial.
     + destruct a; simpl; trivial.
 Qed.

End Extensionnality.





