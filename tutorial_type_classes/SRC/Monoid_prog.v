(**

A variation of Monoid.v, using Program Fixpoint instead of Function *)

Set Implicit Arguments.

Require Import ZArith Arith.
Require Import Mat.
Require Import Div2.
Require Import Program.

Class Monoid {A:Type}(dot : A -> A -> A)(one : A) : Type := {
  dot_assoc : forall x y z:A, dot x (dot y z)= dot (dot x y) z;
  one_left : forall x, dot one x = x;
  one_right : forall x, dot x one = x}.



(*
Print Monoid.


Record Monoid (A : Type) (dot : A -> A -> A) (one : A) : Type := Build_Monoid
  { dot_assoc : forall x y z : A, dot x (dot y z) = dot (dot x y) z;
    one_left : forall x : A, dot one x = x;
    one_right : forall x : A, dot x one = x }

For Monoid: Argument A is implicit
For Build_Monoid: Argument A is implicit
For Monoid: Argument scopes are [type_scope _ _]
For Build_Monoid: Argument scopes are [type_scope _ _ _ _ _]

About one_left.


one_left :
forall (A : Type) (dot : A -> A -> A) (one : A),
Monoid dot one -> forall x : A, dot one x = x

Arguments A, dot, one, Monoid are implicit and maximally inserted
Argument scopes are [type_scope _ _ _ _]
one_left is transparent
Expands to: Constant Top.one_left
*)


Open Scope Z_scope.

Instance ZMult : Monoid  Zmult 1.
Proof.
  split;intros;ring.
Qed.



(*
About one_right.

one_right :
forall (A : Type) (dot : A -> A -> A) (one : A),
Monoid dot one -> forall x : A, dot x one = x

Arguments A, dot, one, Monoid are implicit and maximally inserted
Argument scopes are [type_scope _ _ _ _]
one_right is transparent
Expands to: Constant Top.one_right
*)

Generalizable Variables A dot one.

Fixpoint power `{M: Monoid A dot one}(a:A)(n:nat) :=
  match n with 0%nat => one
             | S p => dot a (power a p)
  end.

Section binary_power. 
  Context `{M: Monoid A dot one}.

  Program
  Fixpoint binary_power_mult
               (acc x:A)(n:nat){measure  n} : A 
   (* acc * (x ** n) *) := let M' := M in
   match n with 0%nat => acc
              | _ => 
               if  Even.even_odd_dec n
               then binary_power_mult  acc (dot x x) (div2 n)
               else binary_power_mult  (dot acc  x) (dot  x  x) (div2 n)
   end.

 Solve Obligations with program_simpl; intros; set(M':=M) ; apply lt_div2; auto with arith.
 Import WfExtensionality.

 Lemma binary_power_mult_equation
         (acc x:A)(n:nat) : binary_power_mult acc x n =
   match n with 0%nat => acc
              | _ => 
               if  Even.even_odd_dec n
               then binary_power_mult acc (dot x x) (div2 n)
               else binary_power_mult (dot acc  x) (dot  x  x) (div2 n)
   end.
 Proof.
   unfold binary_power_mult at 1.
   on_call binary_power_mult_func 
           ltac:(fun c => 
                   unfold_sub @binary_power_mult_func c;
                   fold binary_power_mult_func).
   cbn. destruct n; reflexivity.
 Qed.

 End binary_power.

Definition binary_power `{M:Monoid A dot one} x n := binary_power_mult one x n.


Example Ex1 : binary_power 2 100 = 1267650600228229401496703205376.
Proof. reflexivity. Qed.

(* Example : 2 x 2 Matrices on a ring *)

Section M2_def.
Variables (A:Type)
           (zero one : A) 
           (plus mult minus : A -> A -> A)
           (sym : A -> A).
 Notation "0" := zero.  Notation "1" := one.
 Notation "x + y" := (plus x y).  
 Notation "x * y " := (mult x y).
 
 Variable rt : ring_theory  zero one plus mult minus sym (@eq A).

 Add  Ring Aring : rt.


Global Instance M2_Monoid : Monoid   (M2_mult  plus mult ) (Id2   0 1).
Proof. 
 split.
 - destruct x;destruct y;destruct z;simpl.
   unfold M2_mult; apply M2_eq_intros;simpl;  ring.
 - destruct x;simpl;
   unfold M2_mult; apply M2_eq_intros; simpl; ring.  
 - destruct x;simpl; unfold M2_mult;apply M2_eq_intros;simpl;ring. 
Qed.

End M2_def.

Instance M2Z : Monoid  _ _ := M2_Monoid Zth.

(** Tests : 

 Compute power (Build_M2  1 1 1 0) 40.
 = {|
       c00 := 165580141;
       c01 := 102334155;
       c10 := 102334155;
       c11 := 63245986 |}
     : M2 Z
*)

Definition fibonacci (n:nat) :=
  c00   (power  (Build_M2  1 1 1 0) n).

(* Generic study of power functions *)

Section About_power.


 Context `(M:Monoid A dot one ).


Ltac monoid_rw :=
    rewrite (@one_left A dot one M) || 
    rewrite (@one_right A dot one M)|| 
    rewrite (@dot_assoc A dot one M).

  Ltac monoid_simpl := repeat monoid_rw.

  Local Infix "*" := dot.
  Local Infix "**" := power (at level 30, no associativity).


  Lemma power_x_plus : forall x n p, x ** (n + p) =  x ** n *  x ** p.
  Proof.
   induction n as [| p IHp];simpl.
   - intros;  monoid_simpl;trivial.
   - intro q;rewrite (IHp q);  monoid_simpl;trivial. 
  Qed.

  Ltac power_simpl := repeat (monoid_rw || rewrite <- power_x_plus).

  Lemma power_commute : forall x n p,  
               x ** n * x ** p = x ** p * x ** n. 
  Proof.
   intros x n p;power_simpl; rewrite (plus_comm n p);trivial.
 Qed.

 Lemma power_commute_with_x : forall x n ,  
        x * x ** n = x ** n * x.
 Proof.
  induction n;simpl;power_simpl;trivial.
  repeat rewrite <- (@dot_assoc A dot one M); rewrite IHn; trivial.
 Qed.

 Lemma power_of_power : forall x n p,  (x ** n) ** p = x ** (p * n).
 Proof.
   induction p;simpl;[| rewrite power_x_plus; rewrite IHp]; trivial.
Qed.


Lemma power_S : forall x n, x *  x ** n = x ** S n.
Proof. intros;simpl;auto. Qed.

Lemma sqr : forall x, x ** 2 =  x * x.
Proof.
 simpl;intros;monoid_simpl;trivial.
Qed.

Ltac factorize := repeat (
                rewrite <- power_commute_with_x ||
                rewrite  <- power_x_plus  ||
                rewrite <- sqr ||
                rewrite power_S ||
                rewrite power_of_power).

 Lemma power_of_square : forall x n, (x * x) ** n = x ** n * x ** n.
Proof.
  induction n;simpl;monoid_simpl;trivial.
  repeat rewrite dot_assoc;rewrite IHn; repeat rewrite dot_assoc.
  factorize; simpl;trivial.
 Qed.

Lemma binary_power_mult_ok :
  forall n a x,  binary_power_mult a x n = a * x ** n.
Proof.
  intro n; pattern n;apply lt_wf_ind.
  clear n; intros n Hn;   destruct n.
  - intros;simpl; monoid_simpl;  trivial.
  -  intros; rewrite binary_power_mult_equation. 
     destruct (Even.even_odd_dec (S n)).
     rewrite Hn,  power_of_square;  factorize.
     pattern (S n) at 3;replace (S n) with (div2 (S n) + div2 (S n))%nat;auto.
     generalize (even_double _ e);simpl;auto. 
     apply lt_div2;auto with arith.
     rewrite Hn. 
     rewrite power_of_square ; factorize.
     pattern (S n) at 3;replace (S n) with (S (div2 (S n) + div2 (S n)))%nat;auto.
     rewrite <- dot_assoc; factorize;auto.
     generalize (odd_double _ o);intro H;auto.
     apply lt_div2;auto with arith.
Qed.

Lemma binary_power_ok : forall (x:A) (n:nat), binary_power x n = x ** n.
Proof.
  intros n x;unfold binary_power;rewrite binary_power_mult_ok;
  monoid_simpl;auto.
Qed.

End About_power.



Arguments binary_power_ok [A dot one M] x n.

Class Abelian_Monoid `(M:Monoid ):= {
  dot_comm : forall x y, dot x  y = dot y  x}.

(** Tests :
Print Abelian_Monoid.
*)


Instance ZMult_Abelian : Abelian_Monoid ZMult.
Proof. 
 split; exact Zmult_comm.
Qed.


Section Power_of_dot.
 Context `{M: Monoid A} {AM:Abelian_Monoid M}.
 
Theorem power_of_mult :
   forall n x y, 
    power (dot x y)  n =  dot (power x  n) (power y n). 
Proof.
 induction n;simpl.
 -  rewrite one_left;auto.
 -  intros; rewrite IHn; repeat rewrite dot_assoc.
    rewrite <- (dot_assoc  x y (power x n)); rewrite (dot_comm y (power x n)).
    repeat rewrite dot_assoc;trivial.
Qed.

End Power_of_dot.


(** Tests :

Check power_of_mult 3 4 5.

power_of_mult 3 4 5
     : power (4 * 5) 3 = power 4 3 * power 5 3
*)
 
