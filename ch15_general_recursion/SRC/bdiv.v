Require Export Arith.

Fixpoint bdiv_aux (b m n:nat) {struct b} : nat * nat :=
  match b with
  | O => (0, 0)
  | S b' =>
      match le_gt_dec n m with
      | left H => match bdiv_aux b' (m - n) n with
                  | (q, r) => (S q, r)
                  end
      | right H => (0, m)
      end
  end.

(* Here is the real solution to the exercise.  One of the keys is
  to detect that we are going to prove properties of inequalities
  that can be decided using Omega. *)

Require Export Omega.

Theorem bdiv_aux_correct2 :
 forall b m n:nat, m <= b -> 0 < n -> snd (bdiv_aux b m n) < n.
Proof.
 intros b; induction b as [ | b Hrec]; auto with arith.
 { cbn in |- *;   intros m n Hle Hlt; case (le_gt_dec n m).
   -  generalize (Hrec (m - n) n).
      case (bdiv_aux b (m - n) n); simpl in |- *; intros; omega.
   - simpl in |- *; intros; omega.
  }
Qed.