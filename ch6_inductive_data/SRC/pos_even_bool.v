Require Import ZArith.

Definition pos_even_bool (p:positive) : bool :=
  match p with
  | xO _ => true
  | _ => false
  end.

(* Tests :


Compute pos_even_bool 326%positive.

Compute pos_even_bool 3261%positive.

*)


