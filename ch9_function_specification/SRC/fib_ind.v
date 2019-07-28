Require Import Arith.

Lemma fib_rect :
 forall P:nat -> Type,
   P 0 ->
   P 1 -> 
  (forall n:nat, P n -> P (S n) -> P (S (S n))) ->
  forall n:nat, P n.
Proof.
 intros P H0 H1 HSSn n.
 assert (X: P n *  P (S n)).
 - induction n as [ | n IHn].
  +  split; auto.
  +  destruct IHn; split; auto. 
-  now destruct X. 
Qed.

Definition fib_ind (P : nat -> Prop) := fib_rect P.

Fixpoint fib (n:nat) : nat :=
  match n with
  | O => 1
  | S O => 1
  | S (S p as q) => fib p + fib q
  end.

Lemma fib_SSn : forall n:nat, fib (S (S n)) = fib n + fib (S n).
Proof. reflexivity. Qed.

Require Import Omega Arith.

Lemma fib_SSn_p :
 forall n p:nat, fib (S (S p) + n) = fib (S n) * fib (S p) + fib n * fib p.
Proof.
 intro n; induction  n  as [ | | n Hn HSn] using fib_ind.
 -  cbn;intros;
     repeat rewrite  plus_0_r; rewrite plus_comm; auto.
 -  intro p; replace (S (S p) + 1) with (S (S (S p))) by ring.
    rewrite (fib_SSn (S p)); simpl (fib 2); simpl (fib 1);
    rewrite (fib_SSn p); ring.
 -  intros  p.
    replace (S (S p) + S (S n)) with (S (S (S (S p) + n))) by ring. 
     rewrite (fib_SSn (S (S p) + n)), Hn.
     replace (S (S (S p) + n)) with (S (S p) + S n) by ring. 
     rewrite HSn; rewrite (fib_SSn (S n)); rewrite (fib_SSn n).
    ring.  
Qed.

