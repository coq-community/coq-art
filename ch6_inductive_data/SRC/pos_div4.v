Require Import ZArith.

Definition pos_div4 (n:positive) : Z :=
 match n with 
   | xO (xO p) => Zpos p
   | xI (xO p) => Zpos p
   | xO (xI p) => Zpos p
   | xI (xI p) => Zpos p
   | _ => 0%Z
 end.

(** Tests 
Compute (pos_div4 56%positive).
Compute (pos_div4 55%positive).
Compute (pos_div4 49%positive).
Compute (pos_div4 3%positive).
Compute (pos_div4 4%positive).
*)
