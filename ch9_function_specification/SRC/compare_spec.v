Require Import Arith.
Require Import Omega.
Require Import RelationClasses.
Import Relations.

(*** Specification of a comparison fonction *)
Section A_declared.
Variable A: Type.
Variable lt :  relation A.

Let le  x y := lt x y \/ x = y.

Context (lt_strict : StrictOrder lt).

Inductive CompSpec  (x y:A) : comparison -> Prop :=
 | CompEq : forall (H_eq: x = y), CompSpec  x y Eq
 | CompLt : forall (H_lt:lt x y), CompSpec  x y Lt
 | CompGt : forall (H_gt:lt y x), CompSpec  x y Gt.

Definition correct (cmp: A -> A -> comparison) :=
   forall x y:A, CompSpec x y (cmp x y).

Variable cmp : A -> A -> comparison.


Definition max  (x y:A)  : A :=
match cmp x y with Lt => y | _ => x end.

Definition min  (x y:A) : A :=
match cmp x y with Gt => y | _ => x end.

Section cmp_max_properties.

Hypothesis cmp_ok : correct cmp.

Lemma cmp_eq : forall x:A, cmp x x = Eq.
Proof.
   destruct lt_strict as [Hirr _].
   intro x; destruct (cmp_ok x x).  
   - reflexivity.  
   - now  destruct (Hirr x). 
   - now  destruct (Hirr x). 
Qed.

Lemma cmp_eq_iff : forall x y:A, cmp x y = Eq <-> x = y.
Proof.
 split.
  destruct lt_strict as [Hirr _].
  destruct (cmp_ok x y); auto.
  - discriminate.   
  - discriminate.
  - intro; subst y; now rewrite cmp_eq.
Qed.

Lemma cmp_lt_iff : forall x y:A, cmp x y = Lt <-> lt x y.
Proof.
  destruct lt_strict as [Hirr Htrans]; intros x y;
  destruct (cmp_ok x y);split; auto; try discriminate.
  intro ; subst y; destruct (Hirr x);auto.
  intro; destruct (Hirr x); eapply Htrans; eauto.
Qed.

Lemma cmp_sym : forall x y , cmp x y = Gt <-> cmp y x = Lt.
Proof.
  destruct lt_strict as [Hirr Htrans].
  intros  x y;destruct (cmp_ok x y);destruct (cmp_ok y x);
  split;try discriminate;auto;intros.
  - subst y;  now destruct (Hirr x).
  - destruct (Hirr x); transitivity y;auto.
  - subst y;  now destruct (Hirr x).
  - destruct (Hirr x); transitivity y;auto.
Qed.

Lemma max_eq : forall x y: A, let  m:= max  x y 
                              in m = x \/ m = y.
Proof. 
  intros x y; unfold max; destruct (cmp_ok x y); cbn; auto.
Qed.


Lemma le_max : forall x y:A, le x (max  x y).
Proof. 
  intros x y; unfold le, max; destruct (cmp_ok x y); cbn; auto.
Qed.


Lemma max_le : forall x y z:A, le x z -> le y z -> le (max x y) z.
Proof.
  intros x y z H H0; destruct (max_eq x y) as [e  | e]; now rewrite e.
Qed.


End cmp_max_properties.

End A_declared.

Arguments max {A} _ _ _.

(** let us consider now a comparison function on natural numbers *)

Fixpoint cmp (n p :nat) : comparison :=
  match n, p with 0, 0 => Eq
                | 0, S _ => Lt
                | S _, 0 => Gt
                | S q, S r => cmp q r
  end.

Lemma cmp_correct : correct nat lt cmp. 
Proof.
 red.
 induction x;destruct y;simpl;try constructor;auto with arith.
 destruct (IHx y).
 subst y;constructor;trivial.
 constructor;auto with arith.
 constructor;auto with arith.
Qed.


Compute max  cmp 5 8.














 

