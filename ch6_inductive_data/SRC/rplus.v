Require Import Arith.

Fixpoint rplus (n p:nat) {struct p} : nat :=
  match p with
  | O => n
  | S q => S (rplus n q)
  end.

(** Test :

Compute rplus 33 17.
*)

Theorem rplus_0_p : forall p:nat, rplus 0 p = p.
Proof.
 induction p; simpl; auto.
Qed.

Theorem rplus_Sn_p : forall n p:nat, rplus (S n) p = S (rplus n p).
Proof.
 induction p; simpl; auto.
Qed.

Theorem plus_rplus_equiv : forall n p:nat, n + p = rplus n p.
Proof.
 induction n; simpl.
 - intro p; rewrite rplus_0_p; auto.
 - intro p; rewrite rplus_Sn_p; auto.
Qed.


