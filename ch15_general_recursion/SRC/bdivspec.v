Require Export Arith.
Require Export Lia.
Require Export ArithRing.

Lemma le_plus_minus_r : forall n m : nat, n <= m -> n + (m - n) = m.
Proof.
intros n m Hle.
rewrite (Nat.add_comm n (m - n)), (Nat.sub_add n m Hle).
reflexivity.
Qed.
 
Lemma sub_decrease : forall b n m:nat, n <= S b -> 0 < m -> n - m <= b.
Proof. intros; lia. Qed.

Ltac remove_minus :=
  match goal with
  |  |- context [(?X1 - ?X2 + ?X3)] =>
      rewrite <- (Nat.add_comm X3); remove_minus
  |  |- context [(?X1 + (?X2 - ?X3) + ?X4)] =>
      rewrite <- (Nat.add_assoc X1 (X2 - X3)); remove_minus
  |  |- context [(?X1 + (?X2 + (?X3 - ?X4)))] =>
      rewrite (Nat.add_assoc X1 X2 (X3 - X4))
  |  |- (_ = ?X1 + (?X2 - ?X3)) =>
      apply (fun n m p:nat => proj1 (Nat.add_cancel_l m p n)) with X3;
       try rewrite (Nat.add_shuffle3 X3 X1 (X2 - X3)); 
       rewrite le_plus_minus_r
  end.
 
Definition bdivspec :
  forall b n m:nat,
    n <= b -> 0 < m -> {q : nat &  {r : nat | n = m * q + r /\ r < m}}.
 fix bdivspec 1.
 {  intros b; case b.
    -  intros n m Hle Hlt; rewrite (proj1 (Nat.le_0_r _) Hle);
       exists 0; exists 0; split;
       auto with arith.
       ring.
    - intros b' n m Hle Hlt; case (le_gt_dec m n).
      +  intros Hle';
         generalize (bdivspec b' (n - m) m (sub_decrease b' n m Hle Hlt) Hlt).
         intros [q' [r [Heq Hlt']]];
           exists (S q'); exists r; split; auto with arith.
        replace (m * S q' + r) with (m * q' + r + m).
        rewrite <- Heq;  remove_minus; trivial.
        ring.
      + intros Hgt; exists 0; exists n; split; auto with arith.
         ring.
}
Qed.
