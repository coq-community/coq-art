Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Require Export log2_it.
 
Inductive log_domain : nat ->  Prop :=
 | log_domain_1: log_domain 1
 | log_domain_2:
     forall (p : nat), log_domain (S (div2 p)) ->  log_domain (S (S p)) .
 
Theorem log_domain_non_O: forall (x : nat), log_domain x ->  (x <> 0).
Proof.
 intros x H; case H;  discriminate.
Qed.
 
Theorem log_domain_inv:
 forall (x p : nat), log_domain x -> x = S (S p) ->  log_domain (S (div2 p)).
Proof.
intros x p H; case H; (try (intros H'; discriminate H')).
 intros p' H1 H2; injection H2; intros H3; rewrite <- H3; assumption.
Defined.
 
Fixpoint exp2 (n : nat) : nat :=
 match n with O => 1 | S p => 2 * exp2 p end.
 
Theorem spec_1:  exp2 0 <= 1 < 2 * exp2 0 .
Proof.
simpl; auto with arith.
Qed.
 
Theorem spec_2:
 forall p v',
 ( exp2 v' <= div2 (S (S p)) < 2 * exp2 v' ) ->
  ( exp2 (S v') <= S (S p) < 2 * exp2 (S v') ).
Proof.
intros p v' H; (cbv zeta iota beta delta [exp2]; fold exp2).
elim (div2_eq (S (S p))); intros; omega.
Qed.
 
Definition log_well_spec:
 forall x (h : log_domain x),
  ({v : nat |  exp2 v <= x < 2 * exp2 v }).
refine (fix
        log_well_spec (x : nat) (h : log_domain x) {struct h} :
          {v : nat |  exp2 v <= x < 2 * exp2 v } :=
           match x as y
           return x = y ->  ({v : nat |  exp2 v <= y < 2 * exp2 v })
           with
              0 =>
                fun h' =>
                False_rec
                 ({v : nat |  exp2 v <= 0 < 2 * exp2 v })
                 (log_domain_non_O x h h')
             | 1 =>
                 fun h' =>
                 exist (fun v =>  exp2 v <= 1 < 2 * exp2 v ) 0 spec_1
             | S (S p) =>
                 fun h' =>
                    match log_well_spec (S (div2 p)) (log_domain_inv x p h h')
                     with
                      exist _ v' Hv' =>
                        exist 
                         (fun v =>  exp2 v <= S (S p) < 2 * exp2 v )
                         (S v') (spec_2 p v' Hv')
                    end
           end (refl_equal x)).
Qed.
