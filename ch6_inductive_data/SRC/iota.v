Require Import Arith.
Require Import List.

Definition iota (n:nat) : list nat :=
  (fix f (p:nat)(l:(list nat)){struct p}:list nat :=
       match p with
       | 0 => l 
       | S q => f q ((S q)::l) 
       end) 
   n nil.



(** Test:
Compute  (iota 7).

= 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil
     : list nat
*)

