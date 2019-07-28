Require Export ZArith.

Inductive htree (A:Set) : nat->Set :=
 | hleaf : A->htree A 0
 | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).

Arguments hleaf {A} _.
Arguments hnode {A n} _ _ _.



Fixpoint make_htree_aux (h: nat) (start : Z) : Z * htree Z h :=
match h with 
  | 0 => ((1+ start)%Z, hleaf start)
  | S h' => let p := make_htree_aux h' (1+start)%Z 
            in let q := make_htree_aux h'  (fst p) 
               in (fst q, hnode start (snd p) (snd q))
end.

Definition make_htree (n:nat) : htree Z n :=
 snd (make_htree_aux n 0%Z).

(** Test :

Compute make_htree 3 .

*)
