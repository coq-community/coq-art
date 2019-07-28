Require Export List.
Require Export Omega.

Module Type Comparable_data.
Parameter A : Type.
Parameter Ale : A -> A -> Prop.
Parameter Ale_dec : forall x y:A, {Ale x y} + {Ale y x}.
End Comparable_data.

Module Type SORTING_BASICS.
Parameter A : Type.
Parameter Ale : A -> A -> Prop.
Parameter Ale_dec : forall x y:A, {Ale x y} + {Ale y x}.
Parameter sort : list A -> list A.

Inductive sorted : list A -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall x:A, sorted (x :: nil)
  | sorted2 :
      forall (x y:A) (l:list A),
        Ale x y -> sorted (y :: l) -> sorted (x :: y :: l).

Inductive permutation : list A -> list A -> Prop :=
  | transpose_first :
      forall (a b:A) (l:list A), permutation (a :: b :: l) (b :: a :: l)
  | permutation_same_head :
      forall (a:A) (l1 l2:list A),
        permutation l1 l2 -> permutation (a :: l1) (a :: l2)
  | permutation_empty : permutation nil nil
  | permutation_transitive :
      forall l1 l2 l3:list A,
        permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.

Parameter sort_sorted : forall l:list A, sorted (sort l).

Parameter sort_permutation : forall l:list A, permutation (sort l) l.

End SORTING_BASICS.

Module merge_sort_basics (Data: Comparable_data) : 
  SORTING_BASICS 
  with   Definition A := Data.A 
  with Definition Ale := Data.Ale 
  with Definition  Ale_dec := Data.Ale_dec.

Definition A := Data.A.
Definition Ale := Data.Ale.
Definition Ale_dec := Data.Ale_dec.

Fixpoint merge_aux (l1 l2:list A) (b:nat) {struct b} : 
 list A :=
  match b with
  | O => nil (A:=A)
  | S b' =>
      match l1, l2 with
      | nil, l => l
      | l, nil => l
      | a :: l, b :: l' =>
          match Ale_dec a b with
          | left _ => a :: merge_aux l (b :: l') b'
          | right _ => b :: merge_aux (a :: l) l' b'
          end
      end
  end.

Definition merge (l1 l2:list A) := merge_aux l1 l2 (length l1 + length l2).

(* Make a list of singleton lists to initiate merging. *)

Fixpoint mk_singletons (l:list A) : list (list A) :=
  match l with
  | nil => nil (A:=(list A))
  | a :: tl => (a :: nil) :: mk_singletons tl
  end.

(* Given a list of lists, merge the first with the second,
  then the third with the fourth, and so on. *)

Fixpoint sort_aux1 (l:list (list A)) : list (list A) :=
  match l with
  | l1 :: l2 :: tl => merge l1 l2 :: sort_aux1 tl
  | _ => l
  end.


Fixpoint sort_aux2 (l:list (list A)) (b:nat) {struct b} : 
 list A :=
  match b with
  | O => nil (A:=A)
  | S b' =>
      match l with
      | nil => nil (A:=A)
      | l' :: nil => l'
      | _ => sort_aux2 (sort_aux1 l) b'
      end
  end.

Definition sort (l:list A) := sort_aux2 (mk_singletons l) (length l).

(* In principle the exercise stops here.  But what follows is
  used to ensure that the sorting function we have defined does really
  sort a list of data. *)

Inductive sorted : list A -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall x:A, sorted (x :: nil)
  | sorted2 :
      forall (x y:A) (l:list A),
        Ale x y -> sorted (y :: l) -> sorted (x :: y :: l).


Theorem sorted_inv : forall (a:A) (l:list A), sorted (a :: l) -> sorted l.
Proof.
 intros a l H; inversion H; assumption || constructor.
Qed.


Inductive all_sorted : list (list A) -> Prop :=
  | all_sorted_nil : all_sorted nil
  | all_sorted_rec :
      forall (l:list A) (tl:list (list A)),
        sorted l -> all_sorted tl -> all_sorted (l :: tl).

Theorem mk_singletons_all_sorted :
 forall l:list A, all_sorted (mk_singletons l).
Proof.
 intros l; elim l; simpl in |- *; repeat (intros; constructor || assumption).
Qed.

Theorem mk_singletons_length :
 forall l:list A, length (mk_singletons l) = length l.
Proof.
 simple induction l; simpl in |- *; auto.
Qed.

Inductive first_elem_prop : list A -> list A -> list A -> Prop :=
  | all_empty : first_elem_prop nil nil nil
  | fep_first :
      forall (a:A) (l1 l2 l3:list A), 
        first_elem_prop (a :: l1) l2 (a :: l3)
  | fep_second :
      forall (a:A) (l1 l2 l3:list A), 
       first_elem_prop l1 (a :: l2) (a :: l3).

Theorem merge_aux_sorted :
 forall (b:nat) (l1 l2:list A),
   length l1 + length l2 <= b ->
   sorted l1 ->
   sorted l2 ->
   sorted (merge_aux l1 l2 b) /\ 
   first_elem_prop l1 l2 (merge_aux l1 l2 b).
Proof.
 intros b; elim b.
 -  intros l1 l2.
    case l1; case l2; simpl in |- *;
    try (intros; match goal with
                   | id:(S _ <= _) |- _ => inversion id; fail
                 end).
    repeat constructor.

 -  intros b' Hrec l1; case l1.
    simpl in |- *; intros; split; [ assumption | case l2; constructor ].
    intros a l l2; case l2.
    +  simpl in |- *; intros; split; [ assumption | constructor ].
    +  simpl in |- *; intros a' l' Hle Hsorted1 Hsorted2; case (Ale_dec a a').
       *  elim (Hrec l (a' :: l')); auto.
          intros Hsorted' Hfep.
          generalize Hsorted' Hsorted1 Hsorted2; clear Hsorted1 Hsorted2 Hsorted'. 
          inversion Hfep.
          intros Hsorted' Hsorted1 Hsorted2 Hale.
          inversion Hsorted1; repeat constructor || assumption.
          intros Hsorted' Hsorted1 Hsorted2 Hale.
          inversion Hsorted2; repeat constructor || assumption.
          simpl in |- *; omega.
          eapply sorted_inv; eauto.
       * elim (Hrec (a :: l) l'); auto.
         intros Hsorted' Hfep.
         generalize Hsorted' Hsorted1 Hsorted2; clear Hsorted1 Hsorted2 Hsorted'. 
         inversion Hfep.
         intros Hsorted' Hsorted1 Hsorted2 Hale.
         inversion Hsorted1; repeat constructor || assumption.
         intros Hsorted' Hsorted1 Hsorted2 Hale.
         inversion Hsorted2; repeat constructor || assumption.
         simpl in |- *; omega.
         eapply sorted_inv; eauto.
Qed.

Theorem merge_sorted :
 forall l1 l2:list A, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
 unfold merge in |- *; intros l1 l2 H1 H2; 
  elim (merge_aux_sorted (length l1 + length l2) l1 l2);
  auto.
Qed.

(* sort_aux1 has a multiple recursion step, we need a
   specific induction principle to work on this function. *)

Theorem list_ind2 :
 forall (B:Type) (P:list B -> Prop),
   P nil ->
   (forall x:B, P (x :: nil)) ->
   (forall (x1 x2:B) (l:list B), P l -> P (x1 :: x2 :: l)) ->
   forall l:list B, P l.
Proof.
 intros B P P0 P1 Pr l;assert (H: P l /\  forall x:B, P (x :: l)) by
     (elim l; intuition).
 now destruct H. 
Qed.

Theorem sort_aux1_all_sorted :
 forall l:list (list A), all_sorted l -> all_sorted (sort_aux1 l).
Proof.
 intros l; elim l using list_ind2.
 -  simpl in |- *; trivial.
 -  simpl in |- *; trivial.
 -  intros x1 x2 tl Hrec Has; inversion Has; clear Has.
     match goal with
       | id:(all_sorted _) |- _ => inversion id
     end.
     simpl in |- *; constructor.
     + apply merge_sorted; auto.
     +  auto.
Qed.

Theorem sort_aux1_shorter :
 forall l:list (list A), length (sort_aux1 l) <= length l.
Proof.
 intros l; elim l using list_ind2; simpl in |- *; auto with arith.
Qed.

Theorem sort_aux2_sorted :
 forall (b:nat) (l:list (list A)),
   length l <= b -> all_sorted l -> sorted (sort_aux2 l b).
Proof.
 induction b as [ | b IHb].
 -  intros l; case l.
  +  intros; constructor.
  +  simpl in |- *; intros a l' Hle; inversion Hle.
 - intro  l; case l.
   +  simpl in |- *; intros; constructor.
   +  intros l1 tl; case tl.
      *  intros Hle Has; inversion Has; assumption.
      *  simpl in |- *; intros l2 tl' Hle Has; apply IHb.
         simpl in |- *.
         generalize (sort_aux1_shorter tl'); intros; omega.
         inversion Has; clear Has.
         match goal with
           | id:(all_sorted _) |- _ => inversion id
         end.
         constructor.
         apply merge_sorted; assumption.
         apply sort_aux1_all_sorted; assumption.
Qed.

Theorem sort_sorted : forall l:list A, sorted (sort l).
Proof.
 intros l; unfold sort in |- *.
 apply sort_aux2_sorted.
 rewrite mk_singletons_length; auto.
 apply mk_singletons_all_sorted.
Qed.

Inductive permutation : list A -> list A -> Prop :=
  | transpose_first :
      forall (a b:A) (l:list A), permutation (a :: b :: l) (b :: a :: l)
  | permutation_same_head :
      forall (a:A) (l1 l2:list A),
        permutation l1 l2 -> permutation (a :: l1) (a :: l2)
  | permutation_empty : permutation nil nil
  | permutation_transitive :
      forall l1 l2 l3:list A,
        permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.
        
Theorem permutation_reflexive : forall l:list A, permutation l l.
Proof.
 intros l; elim l; constructor; assumption.
Qed.

Theorem permutation_symmetric :
 forall l1 l2:list A, permutation l1 l2 -> permutation l2 l1.
Proof.
 intros l1 l2 H; elim H; try (intros; constructor; assumption).
 intros l3 l4 l5; intros; apply permutation_transitive with l4; 
  assumption.
Qed.

Theorem permutation_app_cons :
 forall (l:list A) (a:A) (l':list A),
   permutation (l ++ a :: l') (a :: l ++ l').
Proof.
 intros l; elim l.
 simpl in |- *; intros; apply permutation_reflexive.
 simpl in |- *; intros a' tl Hrec a l'.
 apply permutation_transitive with (a' :: a :: tl ++ l'); 
  constructor; auto.
Qed.

Theorem merge_aux_permutation :
 forall (b:nat) (l1 l2:list A),
   length l1 + length l2 <= b -> 
   permutation (merge_aux l1 l2 b) (l1 ++ l2).
Proof.
 intros b; elim b.
 -  intros l1 l2; case l1; case l2;
    try
      (simpl in |- *; intros;
       match goal with
         | id:(S _ <= _) |- _ => inversion id; fail
       end).
    simpl in |- *; constructor.
 -  intros b' Hrec l1 l2; case l1.
    simpl in |- *; intros Hle; apply permutation_reflexive.
    + simpl in |- *; intros a l; case l2.
      simpl in |- *; intros Hle; rewrite <- app_nil_end;
      apply permutation_reflexive.
      simpl in |- *; intros a' l'; case (Ale_dec a a').
      * intros Hale Hle;
        apply permutation_transitive with (a :: a' :: l ++ l').
        apply permutation_same_head.
        apply permutation_transitive with (l ++ a' :: l').
        apply (Hrec l (a' :: l')).
        simpl in |- *; omega.
        apply permutation_app_cons.
        constructor.
        apply permutation_symmetric.
        apply permutation_app_cons.
      *  intros Hale Hle.
         apply permutation_transitive with (a' :: a :: l ++ l').
         apply permutation_same_head.
         apply (Hrec (a :: l) l').
         simpl in |- *; omega.
         apply permutation_transitive with (a :: a' :: l ++ l').
         constructor.
         apply permutation_same_head.
         apply permutation_symmetric.
         apply permutation_app_cons.
Qed.

Theorem merge_permutation :
 forall l1 l2:list A, permutation (merge l1 l2) (l1 ++ l2).
Proof.
 unfold merge in |- *; intros l1 l2; apply merge_aux_permutation; auto.
Qed.

Fixpoint app_all (l:list (list A)) : list A :=
  match l with
  | nil => nil (A:=A)
  | l1 :: tl => l1 ++ app_all tl
  end.

Theorem app_all_mk_singletons_eq :
 forall l:list A, app_all (mk_singletons l) = l.
Proof.
 intros l; elim l; simpl in |- *; auto.
 intros a l' Hrec; rewrite Hrec; auto.
Qed.

Theorem permutation_app :
 forall l1 l2:list A, permutation (l1 ++ l2) (l2 ++ l1).
Proof.
 intros l1; elim l1; simpl in |- *.
 -  intros l2; rewrite <- app_nil_end.
     apply permutation_reflexive.
 - intros a tl Hrec l2.
   apply permutation_transitive with (a :: l2 ++ tl).
   +  apply permutation_same_head.
      apply Hrec.
   + apply permutation_symmetric; apply permutation_app_cons.
Qed.

Theorem permutation_long_head :
 forall l1 l2 l3:list A,
   permutation l2 l3 -> permutation (l1 ++ l2) (l1 ++ l3).
Proof.
 intros l1; elim l1; simpl in |- *; auto.
 intros a l1' Hrec l2 l3 H.
  constructor; auto.
Qed.

Theorem permutation_app4 :
 forall l1 l2 l3 l4:list A,
   permutation l1 l2 ->
   permutation l3 l4 -> permutation (l1 ++ l3) (l2 ++ l4).
Proof.
 intros l1 l2 l3 l4 H H0.
 apply permutation_transitive with (l1 ++ l4).
 -  apply permutation_long_head; assumption.
 -  apply permutation_transitive with (l4 ++ l1).
    +  apply permutation_app.
    +  apply permutation_transitive with (l4 ++ l2).
     *  apply permutation_long_head; assumption.
     * apply permutation_app.
Qed.

Theorem sort_aux1_permutation :
 forall l:list (list A), permutation (app_all (sort_aux1 l)) (app_all l).
Proof.
 intros l; elim l using list_ind2.
 -  simpl in |- *; constructor.
 -  simpl in |- *; intros; apply permutation_reflexive.
 -  intros l1 l2 tl Hrec; simpl in |- *.
    rewrite ass_app.
    apply permutation_app4;auto.
    apply merge_permutation; auto.
Qed.

Theorem sort_aux2_permutation :
 forall (b:nat) (l:list (list A)),
   length l <= b -> permutation (sort_aux2 l b) (app_all l).
Proof.
 intros b; elim b; simpl in |- *; auto.
 -  intros l; case l; simpl in |- *; try constructor.
    intros l' tl H; inversion H.
 -  intros b' Hrec l; case l.
   +  simpl in |- *; intros; constructor.
   +  intros l1 tl; case tl.
      *  simpl in |- *; intros; 
         rewrite <- app_nil_end; apply permutation_reflexive.
      *  intros l2 tl' Hle;
        apply permutation_transitive with 
        (app_all (sort_aux1 (l1 :: l2 :: tl'))).
        apply Hrec.
        simpl in Hle; generalize (sort_aux1_shorter tl').
        simpl in |- *; intros Hle'; omega.
        apply sort_aux1_permutation.
Qed.

Theorem sort_permutation : forall l:list A, permutation (sort l) l.
Proof.
 unfold sort in |- *; intros l; rewrite <- mk_singletons_length.
 pattern l at 3 in |- *; rewrite <- app_all_mk_singletons_eq.
 apply sort_aux2_permutation; auto.
Qed.

(* A nice complement to the exercise would be to define another merge-sorting
  function, but this time using well-founded induction, and yet another
  step would be to use an ad-hoc domain predicate. *)

End merge_sort_basics.
