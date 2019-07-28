Definition eqdec (A:Type) := forall a b : A, {a = b}+{a <> b}.

Definition nat_eq_dec : eqdec nat.
 red; simple induction a; simple destruct b.
 - now left. 
 - right; red; discriminate 1.
 - right; red; discriminate 1.
 -  intro n0; case (H n0); auto. 
Qed.


