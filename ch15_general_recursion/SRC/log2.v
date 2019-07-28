Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Require Export fib_ind.
 
Fixpoint exp2 (n : nat) : nat :=
 match n with 0 => 1 | S p => 2 * exp2 p end.

(** An induction principle adapted to division by two *)

Theorem div2_rect:
 forall (P : nat ->  Type),
 P 0 -> P 1 -> (forall n, P n ->  P (S (S n))) -> forall (n : nat),  P n.
Proof.
intros P X0 X1 Xrec n; assert (P n * P (S n))%type.
 - elim n; intuition.
 - intuition.
Defined.
 
Theorem div2_spec:
 forall n,  ({x : nat | 2 * x = n}) + ({x : nat | 2 * x + 1 = n}).
Proof. 
  intros n; induction  n  as [ | | n Hrec] using div2_rect.
  - left; now exists 0.
  - right; now exists 0.
  - destruct Hrec as  [[x Heq]|[x Heq]].
     + left; exists (S x); rewrite <- Heq; ring.
     + right; exists (S x); rewrite <- Heq; ring.
Qed.
 
Theorem half_smaller0: forall n x, 2 * x = S n ->  (x < S n).
Proof.
 intros; omega.
Qed.
 
Theorem half_smaller1: forall n x, 2 * x + 1 = n ->  (x < n).
Proof.
 intros; omega.
Qed.
 
Definition log2_F:
  forall (n : nat),
    (forall (y : nat),
        y < n -> y <> 0 ->  ({p : nat | exp2 p <= y /\ y < exp2 (p + 1)})) ->
    n <> 0 ->  ({p : nat | exp2 p <= n /\ n < exp2 (p + 1)}).
Proof. 
  intros n; case n.
  - intros log2 Hn0; elim Hn0; trivial.
  - intros n' log2 _; elim (div2_spec (S n')).
    + intros [x]; case_eq x.
      * simpl; intros. subst; discriminate.
      * intros x' Heqx'; assert (Hn0: S x' <> 0) by auto with arith.
        subst x;  destruct (log2 (S x') (half_smaller0 _ _ e) Hn0) as [v Heqv].
        exists (S v); simpl;rewrite <- e;omega.
    + intros [x].  destruct x; simpl.
      *  rewrite <- e.  exists 0; simpl; auto with arith.
      * rewrite <- e. 
        assert (Hn0: S x <> 0) by auto with arith.
        destruct (log2 (S x)) as [a Ha];[ omega | auto | ].
        exists (S a).  simpl.  omega.
Qed.
