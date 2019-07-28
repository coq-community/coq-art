 
Inductive htree (A:Set) : nat -> Set :=
  | hleaf : A -> htree A 0
  | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).
 

Definition first_of_htree :
  forall (A:Set) (n:nat), htree A n -> htree A (S n) -> htree A n.
 intros A n v t.
 generalize v.
 change (htree A (pred (S n)) -> htree A (pred (S n))).
 case t.
 -  intros x v'; exact v'.
 -  intros p x t1 t2 v'; exact t1.
Defined.
 
Theorem injection_first_htree :
 forall (n:nat) (t1 t2 t3 t4:htree nat n),
   hnode nat n 0 t1 t2 = hnode nat n 0 t3 t4 -> t1 = t3.
Proof.
 intros n t1 t2 t3 t4 h.
 change
  (first_of_htree nat n t1 (hnode nat n 0 t1 t2) =
   first_of_htree nat n t1 (hnode nat n 0 t3 t4)).
 now  rewrite h.
Qed.
