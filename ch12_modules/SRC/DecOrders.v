Require Export Relations.

Require Export List.

(* Dictionaries : a dictionary is roughly a partial maping from
   keys to values  *)

(** in coq-8.5beta1, if we replace Set with Type, 
    list_order doesn't compile at line 9 
*)

Module Type DEC_ORDER.
 Parameter A : Set.
 Parameter le : A -> A -> Prop.
 Parameter lt : A -> A -> Prop.
 Axiom ordered : order A le.
 Axiom lt_le_weak : forall a b:A, lt a b -> le a b.
 Axiom lt_diff : forall a b:A, lt a b -> a <> b.
 Axiom le_lt_or_eq : forall a b:A, le a b -> lt a b \/ a = b.
 Parameter lt_eq_lt_dec : forall a b:A, {lt a b} + {a = b} + {lt b a}.
End DEC_ORDER.

(* some derived theorems on dec_orders *)

Module Type MORE_DEC_ORDERS.
 Parameter A : Set.
 Parameter le : A -> A -> Prop.
 Parameter lt : A -> A -> Prop.
 Axiom le_trans : transitive A le.
 Axiom le_refl : reflexive A le.
 Axiom le_antisym : antisymmetric A le.
 Axiom lt_irreflexive : forall a:A, ~ lt a a.
 Axiom lt_trans : transitive A lt.
 Axiom lt_not_le : forall a b:A, lt a b -> ~ le b a.
 Axiom le_not_lt : forall a b:A, le a b -> ~ lt b a.
 Axiom lt_intro : forall a b:A, le a b -> a <> b -> lt a b.
 Parameter le_lt_dec : forall a b:A, {le a b} + {lt b a}.
 Parameter le_lt_eq_dec : forall a b:A, le a b -> {lt a b} + {a = b}.
End MORE_DEC_ORDERS.


(* A functor for getting some useful derived properties on decidable
   orders *)

Module More_Dec_Orders (D: DEC_ORDER) : MORE_DEC_ORDERS with Definition
  A := D.A with Definition le := D.le with Definition lt := D.lt.
                                       
 Definition A := D.A.
 Definition le := D.le.
 Definition lt := D.lt.
 
 Theorem le_trans : transitive A le.
 Proof.
   case D.ordered; auto.
 Qed.

 Theorem le_refl : reflexive A le.
  Proof.
   case D.ordered; auto.
 Qed.
 
 Theorem le_antisym : antisymmetric A le.
 Proof.
   case D.ordered; auto.
 Qed.

 Theorem lt_intro : forall a b:A, le a b -> a <> b -> lt a b.
 Proof.
   intros a b H diff; case (D.le_lt_or_eq a b H); tauto.
 Qed.
 
 Theorem lt_irreflexive : forall a:A, ~ lt a a.  
 Proof.
  intros a H.
  case (D.lt_diff _ _ H); trivial.
 Qed.

 Theorem lt_not_le : forall a b:A, lt a b -> ~ le b a.
 Proof.
  intros a b H H0.
  absurd (a = b).
  apply D.lt_diff; trivial.
  apply le_antisym; auto; apply D.lt_le_weak; assumption.
 Qed.

 Theorem le_not_lt : forall a b:A, le a b -> ~ lt b a.
 Proof.
  intros a b H H0; apply (lt_not_le b a); auto.  
 Qed.

 Theorem lt_trans : transitive A lt.
 Proof.    
  unfold A, transitive in |- *.
  intros x y z H H0.
  apply (lt_intro x z).
  apply le_trans with y; apply D.lt_le_weak; assumption.
  intro e; rewrite e in H.
  absurd (y = z).
  intro e'; rewrite e' in H. 
  apply (lt_irreflexive _ H). 
  apply le_antisym; apply D.lt_le_weak; trivial.
 Qed.

 Definition le_lt_dec : forall a b:A, {le a b} + {lt b a}.
  intros a b; case (D.lt_eq_lt_dec a b).
  intro d; case d; auto.  
  left; apply D.lt_le_weak; trivial. 
  simple induction 1; left; apply le_refl.
  right; trivial.
 Defined.

 Definition le_lt_eq_dec : forall a b:A, le a b -> {lt a b} + {a = b}.
  intros a b H.
  case (D.lt_eq_lt_dec a b).
  trivial. 
  intro H0; case (le_not_lt a b H H0).
 Defined.

End More_Dec_Orders.
