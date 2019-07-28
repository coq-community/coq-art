Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Require Export Wf_nat.
 
Fixpoint div2 (n : nat) : nat :=
 match n with S (S p) => S (div2 p) | _ => 0 end.
 
Theorem div2_ind:
 forall (P : nat ->  Prop),
 P 0 -> P 1 -> (forall n, P n ->  P (S (S n))) -> forall n,  P n.
Proof.
intros P H0 H1 Hstep n.
assert (H : P n /\ P (S n)) by (elim n; intuition).
 now destruct H.
Qed.
 
Theorem div2_lt: forall n,  (div2 (S n) < S n).
Proof.
intros; elim n  using div2_ind; simpl; intros; omega.
Qed.
 
Definition log2_it_F (log2 : nat ->  nat) (n : nat) : nat :=
   match n with
     0 => 0
    | 1 => 0
    | S (S p) => S (log2 (div2 (S (S p))))
   end.
 
Fixpoint iter {A : Type} (f : A ->  A) (k : nat) (a : A) {struct k} : A :=
 match k with   0%nat => a
               | S p => f (iter  f p a) end.

 
Definition log2_terminates:
 forall (n : nat),
  ({v : nat | exists p : nat , forall k g, p < k ->  iter log2_it_F k g n = v }).
Proof. 
 intros n; elim n  using (well_founded_induction lt_wf); clear n.
 intros n; case n.
 - intros; exists 0, 0;  intros k; case k.
   + intros; omega.
   + intros k' g _; simpl; auto.
 - intros n'; case n'.
   + intros; exists 0; exists 0; intros k; case k.
     * intros; omega.
     * intros k' g_; simpl; auto.
   + intros p f; assert (Hlt: div2 (S (S p)) < S (S p))
                 by apply div2_lt.
     destruct (f (div2 (S (S p))) Hlt) as [v Hex];exists (S v).
     destruct Hex as [p' Heq];exists (S p').
     intros k g; case k.
     * intros; omega.
     * intros k' Hltk;rewrite <- (Heq k' g); auto.
       omega.
Qed.
 
Definition log2 (n : nat) : nat :=
   match log2_terminates n with exist _ v _ => v end.
 
Theorem log2_fix_eqn:
 forall n,  log2 n = match n with
                       0 => 0
                      | 1 => 0
                      | S (S p) => S (log2 (div2 (S (S p))))
                     end.
Proof. 
 intros n; unfold log2; case (log2_terminates n); case n.
 - intros v [p Heq]; rewrite <- (Heq (S p) log2); auto.
 - intros n'; case n'.
   + intros v [p Heq];rewrite <- (Heq (S p) log2); auto.
   + intros n'' v [p Heq];case (log2_terminates (div2 (S (S n'')))).
     intros v' [p' Heq'];
     rewrite <- (Heq (S (S (p + p'))) log2),
             <- (Heq' (S (p + p')) log2); auto.
     omega.
     omega.
Qed.
 
Theorem div2_eq: forall n,  2 * div2 n = n \/ 2 * div2 n + 1 = n.
Proof.
intros n; elim n  using div2_ind; simpl; (try omega).
intros n' [Heq|Heq]; omega.
Qed.
 
Fixpoint exp2 (n : nat) : nat :=
 match n with 0 => 1 | S p => 2 * exp2 p end.
 
Theorem log2_power:
 forall n, 0 < n ->  ( exp2 (log2 n) <= n < 2 * exp2 (log2 n) ).
Proof. 
intros n; elim n  using (well_founded_ind lt_wf).
intros x; case x.
- simpl; intros; omega.
- intros x'; case x'.
  + rewrite (log2_fix_eqn 1); simpl; auto with arith.
  + intros p Hrec; elim (Hrec (div2 (S (S p)))).
    * intros Hle Hlt _; rewrite (log2_fix_eqn (S (S p))).
      cbv zeta iota beta delta [exp2]; fold exp2.
      split.
      apply le_trans with (2 * div2 (S (S p))).
      auto with arith.
      elim (div2_eq (S (S p))).
      omega.
      omega.
      apply le_lt_trans with (2 * div2 (S (S p)) + 1).
      elim (div2_eq (S (S p))).
      omega.
      omega.
      omega.
    * apply div2_lt; simpl; auto with arith.
    *  simpl; auto with arith.
Qed.
