Require Arith.


Inductive F: Set :=
| one : F (* 1 *)
| n : F -> F (* 1 + f *)
| d : F -> F (* 1 / (1 + (1 / f)) *)
.

Fixpoint  fraction (f : F) : nat * nat :=
  match f with
  | one => (1,1)
  | n f' => let (a, b) := fraction f' in (a + b, b)
  | d f' => let (a, b) := fraction f' in (a, a + b)
  end.



(** Test:
Compute  fraction (d (d (n (d (d one))))).    

= (4, 11) : nat*nat

 *)


(****************************************************************************

 bonus proof (for readers of chapter 8) :
   Let us admit that a/b is irreducible if
   there exists u, v in Z such that au+bv=1.
   Then fraction f is irreducible for every f

 *****************************************************************************)

Require Import ZArith.

Open Scope Z_scope.
Inductive bezout (a b:nat): Prop :=
  mk_bezout :  forall u v : Z,
    (lt 0 a) -> 
    (lt 0 b) ->
    (Z_of_nat a) * u +  (Z_of_nat b) * v = 1  ->
    bezout a b.

Lemma b_one : bezout 1 1.
Proof. 
  split with 1 0 ; auto.
Qed.

Lemma b_n : forall a b : nat, bezout a b -> bezout (a + b)%nat b.
Proof.
  intros a b H; case H.
  intros u v H0 HA e.
  split with u (v-u).
  -  auto with arith.
  -  auto.
  -  rewrite inj_plus; now  ring_simplify.
Qed.

Lemma b_d : forall a b : nat, bezout a b -> bezout a (a + b)%nat.
Proof.
  intros a b H; case H.
  intros u v H0 HA e.
  split with  (u-v) v.
  -  auto.
  - auto with zarith.
  - rewrite inj_plus;  ring_simplify;
      now  rewrite (Zmult_comm v (Z_of_nat b)).
Qed.

#[export] Hint Resolve b_one b_d b_n : core.

Inductive simplified : nat*nat -> Prop :=
  mk_simpl : forall a b : nat, bezout a b -> simplified (a, b).

Lemma fractionsimplified  : forall f : F, 
    simplified (fraction f).
Proof.
  simple induction f ; simpl.
  -  split ; auto.
  -  intro f0; case (fraction f0).  
     inversion_clear  1;split; auto.
  -  intro f0; case (fraction f0).  
     inversion_clear  1; split; auto.
Qed.


