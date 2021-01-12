Require Import Arith fib_ind.


(* A generalisation of the fibonacci sequence, parameterized by
   its two first items *)

Fixpoint general_fib (a0 a1 n:nat) {struct n} : nat :=
  match n with
  | O => a0
  | S p => general_fib a1 (a0 + a1) p
  end.

Definition fib_tail (n:nat) := general_fib 1 1 n.


(** Test : should return 89

Compute fib_tail 10.

*)


Lemma general_fib_1 : forall a b:nat, general_fib a b 1 = b.
Proof. reflexivity. Qed.


Lemma general_fib_S :
 forall a b n:nat, general_fib a b (S n) = general_fib b (a + b) n.
Proof. reflexivity. Qed. 


Lemma general_fib_2 :
 forall a b n:nat,
   general_fib a b (S (S n)) = general_fib a b n + general_fib a b (S n).
Proof.
 intros a b n; generalize a b; induction n as [ | n IHn].
 - reflexivity.
 - clear a b; intros a b.
   rewrite (general_fib_S _ _ (S (S n))), IHn.
   now rewrite (general_fib_S _ _  (S n)).
Qed.

Lemma linear_fibo_equiv : forall n:nat, fib_tail n = fib n.
Proof.
 intro n; induction n as [| | n IHn IHSn] using fib_ind.
 - reflexivity.  
 - reflexivity.  
 -  unfold fib_tail in *; rewrite general_fib_2.
    rewrite IHn, IHSn; reflexivity.  
Qed.




