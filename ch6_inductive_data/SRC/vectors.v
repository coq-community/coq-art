Require Import Vector.


Fixpoint vector_nth {A:Type}(n:nat)(p:nat)(v:t A p){struct v}
                  : option A :=
  match n,v  with
    _   , nil _ => None
  | 0   , cons _ b  _ _ => Some b
  | S n', cons _ _  p' v' => vector_nth  n'  p' v'
  end.

(* examples *)

Arguments cons {A} h {n}  _ .
Arguments nil {A}.
Arguments vector_nth {A} n {p} v.

Definition v0 := cons true  (cons false  (cons false  nil)).

Lemma test0 : vector_nth 2 v0  = Some false.
Proof. trivial. Qed.

Lemma test1 : vector_nth 7 v0  = None.
Proof. trivial. Qed.


Theorem nth_size : forall {A:Type}(p:nat)(v:t A p)(n:nat), 
  vector_nth n v  = None <-> p <= n.
Proof.
 induction v;simpl; auto. 
 -  intro n; case n; simpl; split; auto with arith. 
 - intro n0;case n0;simpl;split.
   +    discriminate.
   +  inversion 1.
   +  case (IHv n1);auto with arith.
   +  case (IHv n1);auto with arith.
Qed.







 


 
