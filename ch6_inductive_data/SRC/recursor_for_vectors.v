Require Import  Arith.
Set Implicit Arguments.

(** Similar to Vector_Def library, with different names 
*)

Section Vector_definitions.

Variable A : Type.

Inductive vector : nat -> Type :=
| vnil : vector 0
| vcons (h:A)(n:nat)(v: vector n) : vector (S n).


About vector_rect.

(**
 vector_rect :
forall P : forall n : nat, vector n -> Type,
P 0 vnil ->
(forall (n : nat) (v : vector n), P n v -> P (S n) (vcons h v)) ->
forall (n : nat) (v : vector n), P n v
*)

(** Arguments for the recursor vector_rect *)

Let P_head (n:nat)(v: vector n) := n<>0 -> A.
Let P_tail (n:nat)(v: vector n) := n<>0 -> vector (pred n).


Definition  P_head_0 : P_head  vnil.
Proof.
  intro H. now destruct H.
Defined.


Definition  P_tail_0 : P_tail  vnil.
Proof.
  intro H; now destruct H.
Defined.


Definition P_head_S :
 forall (h : A) (n : nat) (v : vector n), P_head  v ->
                                       P_head  (vcons  h  v) .
Proof.
 intros h n v X _; exact h.
Defined. 

Definition P_tail_S :
 forall (h : A) (n : nat) (v : vector n), P_tail  v ->
                                          P_tail  (vcons  h  v) .
Proof.
 intros h n v X _;  exact v.
Defined. 
 


Definition v_head_aux := vector_rect P_head P_head_0 P_head_S.
Check v_head_aux.

Definition v_tail_aux := vector_rect  P_tail P_tail_0 P_tail_S.


Definition v_head (n:nat)(v: vector (S n)) : A :=
  v_head_aux  v (Nat.neq_succ_0 n).

Definition v_tail (n:nat)(v: vector (S n)) : vector n:=
ltac:( refine (v_tail_aux v _); auto).


Definition v_Id  : forall n, vector n -> vector n :=
fun n => match n with 
| 0 => fun v => vnil
|S p => fun v => vcons (v_head v) (v_tail v)
end. 


Compute fun v : vector 0 => v_Id v.

(*
Definition v_Id  : forall n, vector n -> vector n .
 destruct n; intro v.
 - exact vnil.
 - exact (vcons (v_head v) (v_tail v)).   
Qed.
*)


Lemma v_Id_eq : forall n (v:vector n), v = v_Id v.
 intros n v; pattern n ,v;apply vector_rect.
- reflexivity.
- intros.  reflexivity. 
Qed. 


Lemma vector_0 : forall v: vector 0, v = vnil.
intro v. 
  change  vnil with (v_Id v).
 apply v_Id_eq.
Qed.


Lemma vector_S : forall n (v:vector (S n)),
    v = vcons (v_head v) (v_tail v).
Proof.
  intros n v; change (vcons (v_head v) (v_tail v)) with (v_Id v).
  apply v_Id_eq.
Qed.


  End Vector_definitions.

Arguments vnil {A}.

Lemma test1 : v_head  (vcons  42  vnil) =  42.
Proof. reflexivity. Qed.

Lemma test : v_tail  (vcons  42  (vcons 22 vnil)) =  vcons 22 vnil . 
Proof. reflexivity. Qed.

