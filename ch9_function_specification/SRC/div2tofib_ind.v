Require Export Arith.
Require Export ArithRing.

Fixpoint div2 (n:nat):nat:=
  match n with 0 => 0 | 1 => 0 | S (S p) => S (div2 p) end.

Fixpoint rem2 (n:nat):nat:=
  match n with 0 => 0 | 1 => 1 | S (S p) => rem2 p end.

Theorem div2_ind :
  forall P: nat -> Prop,
    P 0 -> P 1 ->
    (forall n, P n -> P (S (S n))) ->
    forall n, P n.
Proof.
 intros P H0 H1 Hstep n.
 assert (P n/\P(S n)).
 elim n; intuition.
 intuition.
Qed.

Fixpoint fib (n:nat) : nat :=
  match n with
    0 => 1
  | 1 => 1
  | S ((S p) as q) => fib p + fib q
  end.

Fixpoint fib2 (n:nat) : nat*nat :=
  match n with
    0 => (1, 1)
  | S p => 
    let (v1, v2) := fib2 p in (v2, v1 + v2)
  end.

Theorem fib_ind :
  forall P : nat -> Prop,
    P 0 -> P 1 ->
    (forall n, P n -> P (S n) -> P (S (S n)))->
    forall n, P n.
Proof.
 intros P H0 H1 Hstep n.
 assert (P n/\P(S n)).
 elim n; intuition.
 intuition.
Qed.

Theorem div2_rem2_eq : forall n, 2 * div2 n + rem2 n = n.
Proof.
 intros n; elim n using div2_ind; try (simpl; auto with arith; fail).
 intros p IHp; pattern p at 3; rewrite <- IHp.
 simpl;ring.
Qed.

Theorem fib_fib2_equiv : forall n, fib n = (fst (fib2 n)).
Proof.
 intros n; elim n using fib_ind; try(simpl;auto with arith;fail).
 intros p IHp IHSp.
 replace (fib (S (S p))) with (fib p + fib (S p)).
 rewrite IHp; rewrite IHSp.
 simpl.
 case (fib2 p); auto.
 auto.
Qed.
