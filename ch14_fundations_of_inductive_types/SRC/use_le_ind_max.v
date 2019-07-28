 
Definition pred_partial: forall (n : nat), n <> 0 ->  nat.
Proof.
 refine (fun n:nat => match n return n <> 0 -> nat 
                      with 0 => fun h  => False_rec _ _
                         | S p => fun h => p
                      end).
 -  now destruct h.
Defined.
 
Scheme
le_ind_max := Induction for le Sort Prop.
 
Theorem le_2_n_not_zero: forall (n : nat), 2 <= n ->  n <> 0.
Proof.
intros n Hle; elim Hle; intros; discriminate.
Qed.
 
Theorem le_2_n_pred:
 forall (n : nat) (h : 2 <= n),  pred_partial n (le_2_n_not_zero n h) <> 0.
Proof.
 intros n h; induction h  using le_ind_max.
 - discriminate.
 - cbn; inversion h; auto.
Qed.

(** 

Extraction pred_partial.

**)
