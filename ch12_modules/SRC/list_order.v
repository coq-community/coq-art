(* (C) Pierre Castéran , LaBRI, Universite Bordeaux 1,
                     Inria Futurs
Dictionaries (after Paulson : ML for the working programmer) *)

Require Export DecOrders.

(* Lexicographic ordering for lists *)

Module List_Order (D: DEC_ORDER) <: DEC_ORDER with Definition
  A := list D.A .

 Module M := More_Dec_Orders D.
 
 Definition A := list D.A .
 
 Fixpoint le (a b:A) {struct a}: Prop  :=
  match a, b with
  | nil, _ => True
  | x::l , y :: l'=> D.lt x y \/ x = y /\ le l l'
  | _ , _ => False
 end.

 Fixpoint lt (a b:A) {struct a}: Prop  :=
  match a, b with
  | x::l , y :: l'=> D.lt x y \/ x = y /\ lt l l'
  | nil , y::l' => True
  | _, _ => False
 end.

 
 Theorem ordered : order A le.
 Proof.
  split.
  - (** reflexivity *)
    intro l; induction l as [ | a l' Il'] ; cbn; auto.
  - (** transitivity *)
    intros l1 ; induction l1; intros l2 l3; destruct l2,l3; cbn; auto. 
     + contradiction.
     + intuition.
       * left; eapply M.lt_trans; eauto.
       *   subst a1; auto. 
       *  subst a0;  auto. 
       * subst a0; right; split; [auto | eauto]. 
   - (** antisymmetry *)
     intros l1; induction l1; intro l2; destruct l2.
     + reflexivity.
     + inversion 2.
     + inversion 1.
     +  inversion 1.
      *  inversion 1.
         absurd (D.lt a0 a0).
         apply M.lt_irreflexive.
         eapply M.lt_trans;eauto. 
         destruct H2 as [H2 H3];subst a0.
         destruct (M.lt_irreflexive _ H0).
     * destruct H0 as [H0 H1].    subst a0; inversion_clear  1.
       destruct (M.lt_irreflexive _ H2).
       destruct H2 as [_ H3].
       rewrite (IHl1 l2);auto.
 Qed.

 Theorem lt_le_weak : forall a b:A, lt a b -> le a b.
 Proof.
  induction a; destruct  b; simpl ; try tauto;  intuition.
 Qed.

 Theorem lt_diff : forall a b:A, lt a b -> a <> b.
 Proof.
  induction a as [| x l IHl]; destruct  b; cbn.  
  - contradiction.
  -   discriminate. 
  -  contradiction. 
  -  intros [H | [H1 H2]].
    + intro e; injection e; intros; subst x;
      apply (M.lt_irreflexive a);  auto.
    +  intro e; injection e; intros; subst a b;  now apply (IHl l).
 Qed.

 Theorem le_lt_or_eq : forall a b:A, le a b -> lt a b \/ a = b.
 Proof.
  induction a as [ |x l IHl]; destruct b; simpl.
  - auto.
  - auto.   
  - contradiction. 
  - intros [H | [H0 H1]]. 
    + left; auto.
    +   destruct (IHl _ H1). 
       * left;auto. 
       *  subst b a; right; auto.
 Qed.


 Definition lt_eq_lt_dec : forall a b:A, {lt a b} + {a = b} + {lt b a}.
 Proof.
   induction a as [| x l IHl]; cbn ; auto.
   -   destruct b; simpl; auto.
   -   destruct b; simpl; auto.
    +  case (D.lt_eq_lt_dec x a); case (IHl b); simpl; auto.
       destruct 1.
      *   destruct 1; auto.
      *   destruct 1;auto.
          subst b a; auto.
      *  destruct 2; auto.
 Defined.

End List_Order. 



