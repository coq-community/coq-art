(* A sorting example : 
   (C) Yves Bertot, Pierre Casteran 
*)

(**
This version uses some new features of Coq : Type Classes and User Defined Relations.

The function called "aux" in the book has been renamed to "insert" and "equiv" has 
been renamed to "permutation".
*)


Require Import List  ZArith RelationClasses Morphisms
               Extraction.
Open Scope Z_scope.

Inductive sorted : list Z -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall z:Z, sorted (z :: nil)
  | sorted2 :
      forall (z1 z2:Z) (l:list Z),
        z1 <= z2 ->
        sorted (z2 :: l) -> sorted (z1 :: z2 :: l).

#[export] Hint Constructors sorted :  sort.

Lemma sort_2357 :
 sorted (2 :: 3 :: 5 :: 7 :: nil).
Proof.
 auto with sort zarith.
Qed.

(**
  inversion lemma 
*)
  
Theorem sorted_inv :
 forall (z:Z) (l:list Z), sorted (z :: l) -> sorted l.
Proof.
 intros z l H; inversion H; auto with sort.
Qed.

(*  Number of occurrences of z in l *)

Fixpoint nb_occ (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => 0%nat
  | (z' :: l') =>
      match Z.eq_dec z z' with
      | left _ => S (nb_occ z l')
      | right _ => nb_occ z l'
      end
  end.

Example ex0 : nb_occ 3 (3 :: 7 :: 3 :: nil) = 2%nat.
Proof. reflexivity. Qed.

(* list l' is a permutation of list l *)

Definition permutation (l l':list Z) : Prop := 
    forall z:Z, nb_occ z l = nb_occ z l'.

(* permutation is an equivalence ! *)

Instance permutation_refl : Reflexive permutation.
Proof.
 intro x; red; trivial.
Qed.

Instance  permutation_sym : Symmetric permutation.
Proof.
 intros x y Hxy ; unfold permutation; auto.
Qed.

Instance permutation_trans : Transitive permutation.
Proof.
 intros l l' l'' H H0 z; rewrite H; now apply H0.
Qed.


Lemma permutation_cons :
 forall (z:Z) (l l':list Z), permutation l l' -> 
                             permutation (z :: l) (z :: l').
Proof.
 intros z l l' H z'; simpl; case (Z.eq_dec z' z); auto. 
Qed.


Instance cons_proper : Proper (eq ==> permutation ==> permutation) (@cons Z).
Proof.
 intros x y Hxy l l' Hll'; subst y; now apply permutation_cons.
Qed.

Lemma permutation_transpose :
 forall (a b:Z) (l l':list Z),
   permutation l l' -> 
   permutation (a :: b :: l) (b :: a :: l').
Proof.
 intros a b l l' H z; simpl.
 case (Z.eq_dec z a); case (Z.eq_dec z b); 
  simpl; case (H z); auto.
Qed.

#[export] Hint Resolve permutation_cons permutation_refl permutation_transpose : sort.


(* insertion of z into l at the right place 
   (assuming l is sorted) 
*)

Fixpoint insert (z:Z) (l:list Z)  : list Z :=
  match l with
  | nil => z :: nil
  | cons a l' =>
      match Z_le_gt_dec z a with
      | left _ =>  z :: a :: l'
      | right _ => a :: (insert z l')
      end
  end.
   

Lemma insert_permutation : forall (l:list Z) (x:Z), 
                  permutation (x :: l) (insert x l).
Proof.
 induction l as [|a l0 H]; simpl ; auto with sort.
 -  intros x; case (Z_le_gt_dec x a);
      simpl; auto with sort.
    +  intro H0; apply permutation_trans with (a :: x :: l0); 
       auto with sort.
Qed.


Lemma insert_sorted :
 forall (l:list Z) (x:Z), sorted l -> sorted (insert x l).
Proof.
 intros l x H; induction  H; simpl; auto with sort.
 -  case (Z_le_gt_dec x z); simpl;  auto with sort zarith.
 -   revert H H0 IHsorted; simpl; 
     case (Z_le_gt_dec x z2) ,  (Z_le_gt_dec x z1); 
       simpl; auto with sort zarith.
Qed.

(* the sorting function *)

Definition sort :
  forall l:list Z, {l' : list Z | permutation l l' /\ sorted l'}.
 induction l as [| a l IHl]. 
 -  exists (nil (A:=Z)); split; auto with sort.
 -  case IHl; intros l' [H0 H1].
    exists (insert a l'); split.
    + transitivity (a::l').
      * now  rewrite H0. 
      * apply insert_permutation.
    +  now apply insert_sorted. 
Defined.

Extraction "insert-sort" insert sort.


