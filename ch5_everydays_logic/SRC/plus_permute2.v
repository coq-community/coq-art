Require Import Arith.

Theorem plus_permute2 : forall n m p:nat, n + m + p = n + p + m.
Proof.
 intros n m p.
 rewrite <- Nat.add_assoc.
 pattern (m + p); rewrite Nat.add_comm.
 rewrite <- Nat.add_assoc; reflexivity.
Qed.


(** Note : using automatic tactics is better : 

*)

Theorem plus_permute2' : forall n m p:nat, n + m + p = n + p + m.
Proof.
 intros n m p; ring.
Qed.

