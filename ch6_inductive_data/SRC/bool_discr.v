(* A manual proof of true<>false *)

Section proof_of_bool_discr.

 Let is_true (b:bool) : Prop :=
   match b with
   | true => True
   | _ => False
   end.

 Theorem bool_discr : true <> false.
 Proof.
  intro e; change (is_true false).
  rewrite <- e; simpl; trivial.
 Qed.

End proof_of_bool_discr.