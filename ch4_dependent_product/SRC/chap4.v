
Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export ZArithRing.
Require Arith.

Parameters (prime_divisor : nat->nat)
           (prime : nat->Prop)
           (divides : nat->nat->Prop).

(** Tests:

Check prime (prime_divisor 220).

Check divides (prime_divisor 220) 220.

Check divides 3.

*)

Parameter binary_word : nat->Set.

Definition short : Set := binary_word 32.
Definition long : Set := binary_word 64.

(** Tests :

Check ~ divides 3 81.

Check (let d := prime_divisor 220 in prime d /\ divides d 220).

*)


Parameters (decomp : nat -> list nat)
           (decomp2 : nat->nat*nat).

(** Tests :

Check decomp 220.

Check decomp2 284.

Check forall n:nat, 2<=n ->
       prime (prime_divisor n) /\
       divides (prime_divisor n) n.
*)

Parameter
  prime_divisor_correct :
     forall n:nat, 2 <= n -> 
       let d := prime_divisor n in prime d /\ divides d n.

Parameter
  binary_word_concat :
     forall n p:nat,
       binary_word n -> binary_word p -> binary_word (n+p).

(* Tests :

Check (forall A B :Set, A->B->A*B).

*)

Definition le_36_37 := le_S 36 36 (le_n 36).

Definition le_36_38 : 36 <= 38 := le_S 36 37 le_36_37.

(** Tests :

Check (le_S _ _ (le_S _ _ (le_n 36))).

Check prime_divisor_correct 220.

*)


Fixpoint iterate (A:Type)(f:A->A)(n:nat)(x:A) : A :=
  match n with
  | O => x
  | S p => f (iterate A f p x)
  end.

(** Tests : 
Check iterate nat.

Check iterate  _ (mult 2).

Check (iterate _ (mult 2) 10).

Compute iterate _ (mult 2) 10 1.


Check binary_word_concat 32.

Check binary_word_concat 32 32.
*)

Arguments iterate {A} _ _ _.
Arguments binary_word_concat {n p} _ _.
Arguments le_S {n m} _.

Definition binary_word_duplicate (n:nat)(w:binary_word n) 
 : binary_word (n+n) :=
  binary_word_concat  w w.

Definition short_concat : short -> short -> long 
                        := @binary_word_concat 32 32.


Theorem le_i_SSi : forall i:nat, i <= S (S i).
Proof (fun i:nat => le_S  (le_S  (le_n i))).


Definition compose {A B C : Type} :  (A->B)->(B->C)->A->C
   := fun f g x => g (f x).

(** Tests :

Check fun (A:Type)(f:Z->A) => compose  Z_of_nat f.

Check compose  Zabs_nat (plus 78) 45%Z.

Check le_i_SSi 1515.

Check le_S  (le_i_SSi 1515).

Check compose (C := Z) S.

Check @le_S 45.

*)

Definition thrice {A:Type} (f:A->A) := compose f (compose f f).


Lemma thrice_as_iter_3 {A:Type} (f: A -> A): thrice f = iterate f 3.
Proof. reflexivity. Qed.

Lemma thrice_thrice {A:Type} (f: A -> A): thrice (thrice f) = iterate f 9.
Proof. reflexivity. Qed.

Definition my_plus : nat->nat->nat := iterate  S.

Definition my_mult (n p:nat) : nat := iterate  (my_plus n) p 0.

Definition my_expt (x n:nat) : nat := iterate (my_mult x) n 1.

Definition ackermann (n:nat) : nat->nat :=
  iterate (fun (f:nat->nat)(p:nat) => iterate  f (S p) 1) 
          n
          S.


(** Tests :
Compute my_plus 9 7.

Compute my_expt 2 5.

*)


(** Tests :


Check forall P:Prop, P->P.

Check fun (P:Prop)(p:P) => p.

Check @refl_equal.
*)

Theorem ThirtySix : 9*4=6*6.
Proof (refl_equal 36).

Definition eq_sym  {A:Type}{x y:A}(h : x=y) : y=x :=
 eq_ind  x (fun z => z=x) (refl_equal x) y h.

(** Tests :
 Check eq_sym  ThirtySix. 

Check conj.

Check or_introl.

Check or_intror.

Check and_ind.
*)

Theorem conj3 : forall P Q R:Prop, P->Q->R->P/\Q/\R.
Proof fun P Q R p q r => conj p (conj q r).

Theorem disj4_3 : forall P Q R S:Prop, R -> P\/Q\/R\/S.
Proof 
 fun P Q R S r => or_intror _ (or_intror _ (or_introl _ r)).

Definition proj1' :  forall A B:Prop, A/\B->A :=
 fun (A B:Prop)(H:A/\B) => and_ind (fun (H0:A)(_:B) => H0) H.

(** Tests :

Check ex (fun z:Z => (z*z <= 37 /\ 37 < (z+1)*(z+1))%Z).

Check ex_intro.

Check ex_ind.

Check and.

*)