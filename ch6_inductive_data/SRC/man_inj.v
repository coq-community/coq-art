 
Inductive htree (A:Set) : nat -> Set :=
  | hleaf : A -> htree A 0
  | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).
 

Definition left_son {A:Set} {n:nat}: forall (t: htree A (S n)), htree A n :=
  fun  t => match t in htree _ (S n) return htree A n with
              hnode _ n a t1 t2 => t1
            end.

Definition left_son_interactive {A:Set} {n:nat}:
  forall (t: htree A (S n)), htree A n.
Proof.
  intro t; change (htree A (pred (S n))).
  destruct t as [a| n0 a t1 t2].
  - exact (hleaf A a).
  - exact t1.
Defined.

Theorem injection_left_son :
  forall (n:nat) (t1 t2 t3 t4:htree nat n),
    hnode nat n 0 t1 t2 = hnode nat n 0 t3 t4 -> t1 = t3.
Proof.
  intros * H; change (left_son (hnode nat n 0 t1 t2) =
                      left_son (hnode nat n 0 t3 t4)).
   now rewrite H.
Qed. 

