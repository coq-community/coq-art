Require Import ZArith.

Record plane : Set := point {abscissa : Z; ordinate : Z}.

Open Scope Z_scope.

Definition manhattan_dist (p1 p2 : plane) : Z :=
 (Z.abs (abscissa p1 - abscissa p2)) +
 (Z.abs (ordinate p1 - ordinate p2)).


(** Test 
 
Compute (manhattan_dist (point 2 5) (point 7 (-9))).

*)
