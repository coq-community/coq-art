Require Import Arith.

Definition lt_3 (n:nat) : bool :=
  match n with
  | O | 1 | 2 => true
  | _ => false
  end.

(** Tests :

Compute lt_3 45.

Compute  lt_3 2.

Print lt_3.

*)

