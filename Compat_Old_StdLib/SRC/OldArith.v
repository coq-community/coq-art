From Coq Require Import Arith. 

(* Upward compatibility with older versions of std_lib 
   To do: move the contents of this section to some module OldArith
 *)

Lemma le_add_sub_r (n m:nat) : n <= m -> n + (m - n) = m. 
Proof. 
  intro H; rewrite Nat.add_comm, Nat.sub_add; [ reflexivity | assumption]. 
Qed.

Lemma sub_add (n m : nat) : n + m - n = m.
Proof. 
  now rewrite Nat.add_comm, Nat.add_sub. 
Qed. 

