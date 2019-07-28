Require Import Arith.
Require Import ArithRing.
Fixpoint div2 (n:nat) : nat :=
  match n with 
  | 0 | 1 => 0
  | S (S p) => S (div2 p)
  end.

Fixpoint mod2 (n:nat) : nat :=
  match n with 
  | 0 => 0
  | 1 => 1
  | S (S p) => mod2 p
  end.

Definition nat_plus2_rect (P: nat -> Type) :
 P 0 -> P 1 ->
 (forall n: nat, P n -> P (S n) -> P (S (S n))) ->
 forall n:nat, P n.
Proof.
 intros H0 H1 HS; assert(X : forall n, (P n * P (S n))).
- induction n; simpl; auto. 
  +  split.
    *  now destruct IHn.
    * destruct IHn;auto.
- intro n; now destruct (X n).
Defined.

 Lemma div2_mod2 : forall n: nat, n = 2 * (div2 n) + mod2 n.
 Proof. 
 intro n; induction n as [ | | n IHn IHSn] using nat_plus2_rect  ; auto.
 -  cbn;  rewrite IHn at 1; ring.
Qed.

