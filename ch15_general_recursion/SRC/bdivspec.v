Require Export Arith.
Require Export Omega.
Require Export ArithRing.
 
Lemma sub_decrease : forall b n m:nat, n <= S b -> 0 < m -> n - m <= b.
Proof. intros; omega. Qed.

Ltac remove_minus :=
  match goal with
  |  |- context [(?X1 - ?X2 + ?X3)] =>
      rewrite <- (plus_comm X3); remove_minus
  |  |- context [(?X1 + (?X2 - ?X3) + ?X4)] =>
      rewrite (plus_assoc_reverse X1 (X2 - X3)); remove_minus
  |  |- context [(?X1 + (?X2 + (?X3 - ?X4)))] =>
      rewrite (plus_assoc X1 X2 (X3 - X4))
  |  |- (_ = ?X1 + (?X2 - ?X3)) =>
      apply (fun n m p:nat => plus_reg_l m p n) with X3;
       try rewrite (plus_permute X3 X1 (X2 - X3)); 
       rewrite le_plus_minus_r
  end.
 
Definition bdivspec :
  forall b n m:nat,
    n <= b -> 0 < m -> {q : nat &  {r : nat | n = m * q + r /\ r < m}}.
 fix bdivspec 1.
 {  intros b; case b.
    -  intros n m Hle Hlt; rewrite <- (le_n_O_eq _ Hle);
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
