

Theorem all_equal : forall x y : Empty_set, x = y.
Proof.
 destruct x.
Qed.


Theorem all_diff : forall x y : Empty_set, x <> y.
Proof.
 destruct x.
Qed.

