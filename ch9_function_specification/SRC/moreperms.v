Require Import List Arith.
Set  Implicit Arguments.
Import Peano.
 
Section perms.
Variable A : Type.
 
Inductive transpose : list A -> list A ->  Prop :=
  transpose_hd:
    forall (a b : A) (l : list A),  transpose (a :: (b :: l)) (b :: (a :: l))
 | transpose_tl:
     forall (a : A) (l l' : list A),
     transpose l l' ->  transpose (a :: l) (a :: l') .
 
Inductive perm (l : list A) : list A ->  Prop :=
  perm_id: perm l l
 | perm_tr:
     forall (l' l'' : list A), perm l l' -> transpose l' l'' ->  perm l l'' .
 
Variable A_eq_dec : forall a b:A, {a = b} + {a <> b}.
 
Fixpoint nb_occ (a : A) (l : list A)  : nat :=
 match l with
  | nil => 0
  | x :: l' =>
      match A_eq_dec  a x with
        | left _ => S (nb_occ a l')
        | right _ => nb_occ a l'
      end
 end.

 
Lemma transpose_nb_occ:
 forall (l l' : list A),
 transpose l l' -> forall (a : A),  nb_occ a l = nb_occ a l'.
Proof.
intros l l' H; elim H; simpl.
- intros a b l0 x; case (A_eq_dec x a); case (A_eq_dec x b); simpl; auto.
- intros a l0 l'0 H0 H1 x; case (A_eq_dec x a); simpl; auto.
Qed.
 
Lemma perm_nb_occ:
 forall (l l' : list A),
 perm l l' -> forall (a : A),  nb_occ a l = nb_occ a l'.
Proof.
intros l l' H; elim H; auto.
intros l'0; intros; transitivity (nb_occ a l'0);auto.
apply transpose_nb_occ; auto.
Qed.
 

(* What follows is the solution to the last exercise proposed 
  in the chapter on reflexion.  It uses a computation of numbers
  of occurrences to decide that two lists are not equal. *)
 
Fixpoint check_all_occs (l1 l2 l3 : list A)  : bool :=
 match l3 with
   nil => true
  | a :: tl =>
      if Nat.eqb  (nb_occ a l1) (nb_occ a l2) then check_all_occs l1 l2 tl
        else false
 end.
 
Theorem eq_nat_bool_false:
 forall n1 n2, Nat.eqb n1 n2 = false ->   n1 <> n2.
Proof.
induction n1; destruct n2; simpl; intros; discriminate || auto.
Qed.
 
Theorem check_all_occs_false:
 forall l1 l2 l3,
 check_all_occs l1 l2 l3 = false ->
  (exists a : A , nb_occ a l1 <> nb_occ a l2 ).
Proof. 
 simple induction l3.
 - simpl; intros; discriminate.
 - intros n l IHl; simpl.
  generalize (@eq_nat_bool_false (nb_occ n l1) (nb_occ n l2)).
  case (Nat.eqb (nb_occ n l1) (nb_occ n l2)).
  + auto.
  + intros; exists n; auto.
Qed.
 
Theorem check_all_occs_not_perm:
 forall l1 l2, check_all_occs l1 l2 l1 = false ->  ~ perm l1 l2.
Proof. 
intros l1 l2 Heq Hperm; elim (check_all_occs_false l1 l2 l1 Heq); intros n Hneq;
 elim Hneq; apply perm_nb_occ; assumption.
Qed.
 

End perms.

Arguments perm {A} _ _.

Ltac
noperm eqdec := match goal with
          | |- ~ perm ?l1 ?l2 => apply (check_all_occs_not_perm  eqdec) end.

Require Import Peano_dec.
Theorem not_perm2:
 ~ perm (1 :: (3 :: (2 :: nil))) (3 :: (1 :: (1 :: (4 :: (2 :: nil))))).
Proof. now noperm eq_nat_dec. Qed.



