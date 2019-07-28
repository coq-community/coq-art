(** 2-2-matrices over a ring A *)

Require Import Ring.

Section matrices.
 Variables (A:Type)
           (zero one : A) 
           (plus mult minus : A -> A -> A)
           (sym : A -> A).
 Notation "0" := zero.  Notation "1" := one.
 Notation "x + y" := (plus x y).  
 Notation "x * y" := (mult x y).

 Variable rt : ring_theory  zero one plus mult minus sym (@eq A).

 Add Ring Aring : rt.  

Structure M2 : Type := {c00 : A;  c01 : A;
                        c10 : A;  c11 : A}.

Definition Id2 : M2 := Build_M2 1 0 0 1.

Definition M2_mult (m m':M2) : M2 :=
 Build_M2 (c00 m * c00 m' + c01 m * c10 m')
          (c00 m * c01 m' + c01 m * c11 m')
          (c10 m * c00 m' + c11 m * c10 m')
          (c10 m * c01 m' + c11 m * c11 m').



Lemma M2_eq_intros : forall a b c d a' b' c' d',
  a=a' -> b=b' -> c=c' -> d=d' ->
   Build_M2 a b c d = Build_M2 a' b' c' d'.
Proof. 
 intros; now f_equal.
Qed.

End matrices.

Arguments Build_M2 {A} _ _ _ _.
Arguments M2_mult {A} _ _ _  _.
Arguments c00 {A} _.
Arguments Id2 {A} zero one.
