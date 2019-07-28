Require Import Arith Omega.

Definition Even (n:nat) : Prop :=
 exists p:nat, n = 2*p. 

Definition Odd (n:nat) : Prop :=
 exists p:nat, n = S (2*p).


 Lemma Even_not_Odd : forall n, Even n -> ~ Odd n. 
 Proof.
  intros n [p Hp] [q Hq]; rewrite Hp in Hq. 
  omega.
 Qed.

(** Specification of a boolean test for even-ness 
*)

Inductive even_spec (n:nat) : bool -> Prop :=
| even_true : forall (Heven : Even n), even_spec n true 
| even_false : forall (Hodd : Odd n), even_spec n false.

Definition even_test_ok (f : nat -> bool) :=
 forall n:nat, even_spec n (f n).



Fixpoint even_bool (n:nat) :=
 match n with
   | 0 => true
   | 1 => false
   | S (S p)=> even_bool p
end.

(** For proving even_bool's correctness, we shall use an induction principle
    adaptated to its control structure *)


Lemma nat_double_rect : forall (P:nat->Type),
     P 0 -> P 1 -> (forall p, P p -> P (S (S p))) ->
    forall n:nat, P n.
Proof.
 intros P H0 H1 HS.
 assert (X : forall n, (P n *  P (S n)%type)).
 -  induction n as  [| p IHp]; [auto |  destruct IHp;auto].
 - intro n; now destruct (X n).
Qed.

   
Lemma even_spec_SS : forall n b, even_spec n b -> even_spec (S (S n)) b.
Proof.
  intros n p [[q Hq] | [q Hq]]; constructor;exists (S q);omega.
Qed.

Lemma even_bool_correct : even_test_ok  even_bool. 
Proof.
 intro n;induction n using nat_double_rect.
  constructor;exists 0;trivial.
  constructor;exists 0;trivial.
  cbn;apply even_spec_SS;assumption. 
Qed.


(** even_bool_correct can now be used with destruct tactic :


Check even_spec_ind.

even_spec_ind
     : forall (n : nat) (P : bool -> Prop),
       (Even n -> P true) ->
       (Odd n -> P false) -> forall b : bool, even_spec n b -> P b


*)

Lemma even_bool_false (f: nat->bool) (H: even_test_ok f):
 forall n,  Odd n <-> f n = false.
Proof. 
 intros n ;destruct (H n).
-  split;try discriminate;intro;destruct (Even_not_Odd n);auto.
- tauto. 
Qed.







