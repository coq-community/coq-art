Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Require Export Wf_nat.

Section div_it_assumed.

Parameter div_it : forall (n m : nat), 0 < m ->  nat * nat.
 
Hypothesis
   div_it_fix_eqn :
   forall (n m : nat) (h : 0 < m),
    div_it n m h = match le_gt_dec m n with
                     left H => let (q, r) := div_it (n - m) m h in (S q, r)
                    | right H => (0, n)
                   end.
 
Theorem div_it_correct1:
 forall (m n : nat) (h : 0 < n),
  m = fst (div_it m n h) * n + snd (div_it m n h).
Proof.
intros m; induction m  as [m' Hrec]  using (well_founded_ind lt_wf).
intros  n h; rewrite div_it_fix_eqn.
case (le_gt_dec n m'); intros H; trivial.
pattern m' at 1; rewrite (le_plus_minus n m'); auto.
pattern (m' - n) at 1; rewrite Hrec with (m' - n) n h; auto with arith.
case (div_it (m' - n) n h); simpl; auto with arith.
Qed.
 
Theorem div_it_correct2:
 forall (m n : nat) (h : 0 < n),  (snd (div_it m n h) < n).
Proof. 
 intros m; induction m  as [m' Hrec]  using (well_founded_ind lt_wf).
 intros  n h; rewrite div_it_fix_eqn.
 case (le_gt_dec n m'); intros H.
 + assert (Hlt: m'-n < m') by auto with arith.
   generalize (Hrec (m'- n) Hlt n h); case (div_it (m'-n) n h); simpl; auto.
 + simpl; auto.
Qed.

End div_it_assumed.
