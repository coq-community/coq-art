Require Import Bool.
Definition bool_not (b:bool) : bool := if b then false else true.


Definition bool_xor (b b':bool) : bool := if b then bool_not b' else b'.

Definition bool_and (b b':bool) : bool := if b then b' else false.

Definition bool_or (b b':bool) := if b then true else b'.


Definition bool_eq (b b':bool) := if b then b' else bool_not b'.
             

Theorem bool_xor_not_eq :
 forall b1 b2:bool, bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof.
  destruct b1, b2; reflexivity.
Qed.

Theorem bool_not_and :
 forall b1 b2:bool,
   bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2).
Proof.
 destruct b1, b2; reflexivity.
Qed.

Theorem bool_not_not : forall b:bool, bool_not (bool_not b) = b.
Proof.
 now destruct b.
Qed.

Theorem bool_ex_middle : forall b:bool, bool_or b (bool_not b) = true.
Proof.
 now destruct b.
Qed.

Theorem bool_eq_reflect : forall b1 b2:bool, bool_eq b1 b2 = true -> b1 = b2.
Proof.
  destruct  b1, b2; (reflexivity || discriminate).
Qed.

Theorem bool_eq_reflect2 : forall b1 b2:bool, b1 = b2 -> bool_eq b1 b2 = true.
Proof.
 destruct b1, b2; trivial; discriminate.
Qed.

Theorem bool_not_or :
 forall b1 b2:bool,
   bool_not (bool_or b1 b2) = bool_and (bool_not b1) (bool_not b2).
Proof.
   now destruct b1, b2.
Qed.


Theorem bool_or_and_distr :
 forall b1 b2 b3:bool,
   bool_or (bool_and b1 b3) (bool_and b2 b3) = bool_and (bool_or b1 b2) b3.
Proof.
 now destruct b1, b2, b3.  
Qed.
