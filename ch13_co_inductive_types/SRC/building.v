Set Implicit Arguments.
Require Export List  Ltree  ZArith.
Open Scope positive_scope.


(** Infinite tree such that any node labelled with p 
    has a left son labelled with 2p and a right son labelled with 2p+1 
*)

 
CoFixpoint Positive_Tree_from  (p:positive) : LTree positive :=
  LBin p (Positive_Tree_from (xO p)) (Positive_Tree_from (xI p)).

Definition All_Positive_Tree := Positive_Tree_from 1.

(** Tests *)
Example Ex1 :
  LTree_label All_Positive_Tree (d0 :: d1 :: nil) = Some  5.
Proof. reflexivity. Qed.

Example Ex2 :
  LTree_label All_Positive_Tree (d0 :: d1 ::d1 :: nil) = Some 11.
Proof. reflexivity. Qed.

Example Ex3 :
 LTree_label All_Positive_Tree (d0 :: d1 :: d1 :: d0 :: d0 ::d1 :: nil) =
  Some 89.
Proof. reflexivity. Qed.







