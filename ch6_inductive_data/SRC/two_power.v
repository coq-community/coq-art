Require Import Arith.

Fixpoint exp2 (n:nat) : nat :=
  match n with
  | O => 1
  | S p => 2 * exp2 p
  end.

(** Tests: *)

Lemma test: exp2 5 = 32.
Proof. reflexivity. Qed.




