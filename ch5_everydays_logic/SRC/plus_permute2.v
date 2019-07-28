Require Import Arith.

Theorem plus_permute2 : forall n m p:nat, n + m + p = n + p + m.
Proof.
 intros n m p.
 rewrite plus_assoc_reverse.
 pattern (m + p); rewrite plus_comm.
 rewrite plus_assoc_reverse; reflexivity.
Qed.


(** Note : using automatic tactics is better : 

*)

Theorem plus_permute2' : forall n m p:nat, n + m + p = n + p + m.
Proof.
 intros n m p; ring.
Qed.

