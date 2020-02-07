(* Examples of type classes and Setoids *)
(* Version with operational classes *)
(* Some comments by Matthieu *)



Set Implicit Arguments.

Require Import ZArith  Div2  Recdef  Mat.


Class monoid_binop (A:Type) := monoid_op : A -> A -> A.

Declare Scope M_scope.
Delimit Scope M_scope with M.
Infix "*" := monoid_op: M_scope.
Open Scope M_scope.

Class Monoid (A:Type)(dot : monoid_binop  A)(one : A) : Prop := {
  dot_assoc : forall x y z:A, x * (y * z)=  x * y * z;
  one_left : forall x, one * x = x;
  one_right : forall x,  x * one = x}.

(*
one_right :
forall (A : Type) (dot : monoid_binop A) (one : A),
Monoid dot one -> forall x : A, x * one = x
*)



Open Scope Z_scope.

(** Tests :

Compute (@monoid_op _ Zmult 5 6).

*)


Instance Zmult_op : monoid_binop Z | 17:= Zmult.

Instance ZMult : Monoid   Zmult_op  1 | 22.
Proof.
  split;intros; unfold Zmult_op, monoid_op; ring. 
Defined.

Require Import Ring.

Section matrices.
 Variables (A:Type)
           (zero one : A) 
           (plus mult minus : A -> A -> A)
           (sym : A -> A).
 Notation "0" := zero.
 Notation "1" := one.
 Notation "x + y" := (plus x y).  
 Notation "x * y " := (mult x y).
 


 Variable rt : ring_theory  zero one plus mult minus sym (@eq A).

 Add  Ring Aring : rt.

Global Instance M2_mult_op :  monoid_binop (M2 A) := (M2_mult  plus mult ) . 


Global Instance M2_Monoid : Monoid  M2_mult_op (Id2  0 1).
Proof.
  split.
  - destruct x;destruct y;destruct z;unfold monoid_op;simpl.
    unfold M2_mult;apply M2_eq_intros;simpl;  ring.
  - destruct x;simpl;unfold M2_mult_op, monoid_op;
    unfold M2_mult; apply M2_eq_intros; simpl;ring.
  - destruct x;simpl;unfold M2_mult_op, monoid_op;
    unfold M2_mult;apply M2_eq_intros;simpl;ring. 
Defined.

End matrices.

Generalizable Variables A dot one.


Instance M2_Z_op : monoid_binop (M2 Z) := M2_mult Zplus Zmult . 

Instance M2_mono_Z : Monoid (M2_mult_op _ _)  (Id2  _ _):=  M2_Monoid Zth.

(** Tests :

Compute let m := Build_M2 1 1 1 0 in
          (m  *  m)%M.
*)


Fixpoint power `{M : @Monoid A dot one}(a:A)(n:nat) :=
  match n with 0%nat => one
             | S p => (a * power a p)%M
  end.


Infix "**" := power (at level 30, no associativity):M_scope.

(** Tests :
Compute  (2 ** 5) ** 2.

Compute (Build_M2  1 1 1  0) **    40. 
*)


(* A tail recursive linear function *)

Fixpoint power_mult `{M : Monoid }
     (acc x:A)(n:nat) : A (*  acc * (x ** n) *) :=
  match n with 0%nat => acc
             | S p => power_mult (acc * x)%M x p
  end.

Definition tail_recursive_power  `{M : Monoid}(x:A)(n:nat) :=
     power_mult one x n.

Require Import Recdef  Div2.

Function binary_power_mult (A:Type)(dot:monoid_binop A)(one:A) 
    (M: @Monoid A dot one) (acc x:A)(n:nat){measure (fun i=>i) n} : A 
  (* acc * (x ** n) *) :=
  match n with 0%nat => acc
             | _ => match Even.even_odd_dec n
                    with left H0 => binary_power_mult    _   acc (dot x x) (div2 n)
                       | right H1 => 
                         binary_power_mult   _  (acc * x)%M ( x * x)%M (div2 n)
                    end
  end.
Proof. 
  - intros;apply lt_div2; auto with arith.
  - intros;apply lt_div2; auto with arith.
Defined.



Definition binary_power `{M: Monoid} (x:A)(n:nat)  := 
     binary_power_mult    M one  x n.

(** Tests 

Compute binary_power  2 5.

Compute  (Build_M2 1 1 1 0) ** 10.

Compute binary_power (Build_M2 1 1 1 0) 20.
*)



Section About_power.

  Context      `(M:Monoid  ).
  Open Scope M_scope.

  
  Ltac monoid_rw :=
    rewrite one_left || rewrite one_right || rewrite dot_assoc.

  Ltac monoid_simpl := repeat monoid_rw.

  Lemma power_x_plus : forall x n p, (x ** (n + p) = x ** n * x ** p).
  Proof.
   induction n;simpl. 
   - intros; monoid_simpl;trivial.
   - intro p;rewrite (IHn p); monoid_simpl;trivial.
  Qed.

  Ltac power_simpl := repeat (monoid_rw || rewrite <- power_x_plus).

  Lemma power_commute : forall x n p,  
               x ** n * x ** p = x ** p * x ** n. 
  Proof.
   intros x n p;power_simpl;  rewrite (plus_comm n p);trivial.
 Qed.

 Lemma power_commute_with_x : forall x n ,  
        x * x ** n = x ** n * x.
 Proof.
  induction n;simpl;power_simpl;trivial.
  repeat rewrite <- dot_assoc; rewrite IHn; trivial.
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

 Lemma power_mult_correct : 
    forall n x, tail_recursive_power x n = x ** n.
  Proof.
    intros n x;  unfold tail_recursive_power.
    rewrite <-  (one_left  (power x n)).
    assert (forall y:A, power_mult y x n =  y * (power x n)); auto.
       generalize n x;intro p; induction p;simpl;intros; monoid_simpl;auto.
  Qed.

Lemma binary_power_mult_ok :
  forall n a x,  binary_power_mult  M a x n = a * x ** n.
Proof.
  intro n; pattern n;apply lt_wf_ind.
  clear n; intros n Hn;   destruct n.
  -  intros;simpl; rewrite binary_power_mult_equation;monoid_simpl;
    trivial.
  - intros;  
    rewrite binary_power_mult_equation; destruct (Even.even_odd_dec (S n)).
   + rewrite Hn.
     * rewrite power_of_square;  factorize.
       pattern (S n) at 3;replace (S n) with (div2 (S n) + div2 (S n))%nat;auto.
       generalize (even_double _ e);simpl;auto. 
     *  apply lt_div2;auto with arith.
   +  rewrite Hn.
      * rewrite power_of_square ; factorize.
        pattern (S n) at 3;replace (S n) with (S (div2 (S n) + div2 (S n)))%nat;auto.
        rewrite <- dot_assoc; factorize;auto.
        generalize (odd_double _ o);intro H;auto.
      * apply lt_div2;auto with arith.
Qed.

Lemma binary_power_ok : forall x n, binary_power (x:A)(n:nat) = x ** n.
Proof.
  intros n x;unfold binary_power;rewrite binary_power_mult_ok;
  monoid_simpl;auto.
Qed.

End About_power.

(** An efficient Fibonacci function 
*)

Definition fibonacci (n:nat) :=
      c00  (binary_power (Build_M2 1 1 1 0) n).

(** Tests:

Compute fibonacci 20. 
*)

(** Abelian Monoids 
*)

Class Abelian_Monoid `(M:Monoid):= {
  dot_comm : forall x y, (x * y = y * x)%M}.

Instance ZMult_Abelian : Abelian_Monoid ZMult.
Proof. 
  split. 
  - exact Zmult_comm.
Defined.

Section Power_of_dot.
 Context `{M: Monoid A} {AM:Abelian_Monoid M}.

 Open Scope M_scope.
 
 Theorem power_of_mult :
   forall n x y, ((x * y) ** n =  x ** n  * y ** n)%M. 
Proof.
 induction n;simpl.
 -  rewrite one_left;auto.
 - intros; rewrite IHn; repeat rewrite dot_assoc.
   rewrite <- (dot_assoc  x y (power x n)); rewrite (dot_comm y (power x n)).
   repeat rewrite dot_assoc;trivial.
Qed.

End Power_of_dot.


Example Ex1:  forall (x y z :Z)(n:nat),  ((x * (y * z)) ** n  =
                        x ** n *  (y ** n  * z ** n))%M.
Proof. 
intros; repeat (rewrite power_of_mult); trivial. 
Qed.


(*** Monoids with equivalence *)

Require Import Coq.Setoids.Setoid  Morphisms.

Class Equiv A := equiv : relation A.
Infix "==" := equiv (at level 70):type_scope.

  Open Scope M_scope.

  Class EMonoid (A:Type)(E_eq :Equiv A)(E_dot : monoid_binop A)(E_one : A):={
  E_rel :> Equivalence equiv; 
  dot_proper :> Proper (equiv ==> equiv ==> equiv) monoid_op; 
  E_dot_assoc : forall x y z:A,
      x * (y * z) == x * y * z;
  E_one_left : forall x, E_one * x == x;
  E_one_right : forall x, x * E_one == x}.

Generalizable Variables E_eq E_dot E_one.

(* --- *)

Lemma E_trans  `(M:EMonoid A)  : transitive A  E_eq.
Proof. apply E_rel. Qed.

(* The above proofs are equivalent to the overloaded reflexivity, symmetry and transitivity
   lemmas, already avalable for every EMonoid. i.e.: *)


Lemma E_refl' `(M:EMonoid A) : reflexive A  E_eq. 
Proof. intro. change (equiv x x). apply reflexivity. Qed.



Fixpoint Epower `{M : EMonoid }(a:A)(n:nat):A :=
  match n with 0%nat => E_one 
             | S p =>  a * (Epower a p)
  end.


Global Instance  Epower_Proper `(M: EMonoid):
  Proper (equiv ==> Logic.eq ==> equiv) Epower.
Proof.
  intros x y H n p e;subst p;induction n.
  -  reflexivity.
  -  apply dot_proper;auto. 
Qed.



Program Instance monoid_op_params : Params (@monoid_op) 2.

Lemma Epower_x_plus `(M: EMonoid) : 
   forall x n p,  (Epower x (n + p)) == 
                  (Epower x n) * (Epower x p).
  Proof.
   induction n;simpl. 
   -  intros ; rewrite E_one_left;reflexivity.
   -  intro p;  rewrite <- E_dot_assoc;  now rewrite <- IHn.
  Qed.


Lemma Epower_x_mult `(M: EMonoid) : 
   forall x n p,  (Epower x (n * p)) == 
                  Epower (Epower x p) n.
  Proof.
   induction n;simpl. 
   - reflexivity.
   -intro p; rewrite Epower_x_plus;  now rewrite IHn.
 Qed.

(*** The monoid of function composition *)

Section Definitions.
  Variable A : Type.

  Definition  comp (g f : A -> A): A -> A :=
   fun x :A => g (f x).


  Definition fun_ext (f g: A -> A) :=
   forall x , f x  = g x.

  Lemma fun_ext_refl : reflexive (A -> A)  fun_ext.
  Proof. intros  f x; reflexivity. Qed.

  Lemma fun_ext_sym : symmetric (A -> A)  fun_ext.
 Proof. 
  intros f g H x ; rewrite H; reflexivity.
 Qed.

 Lemma fun_ext_trans: transitive (A -> A)  fun_ext.
 Proof. 
   intros f g h H H0 x; rewrite H;rewrite H0;reflexivity. 
 Qed.
  
 (* Global instances are not forgotten at the end of sections and keep their visibility. *)

 Global Instance fun_ext_equiv : Equivalence   fun_ext.
  Proof.
    split; [ apply fun_ext_refl| apply fun_ext_sym| apply fun_ext_trans].
  Qed.

End Definitions.

Instance fun_ext_op A : Equiv (A->A) := @fun_ext A.

(* Comp is proper for extensional equality of functions *)
Global Instance comp_proper A : Proper (equiv ==> equiv ==> equiv) (@comp A).
Proof. reduce; unfold comp; rewrite H, H0; reflexivity. Qed.

Instance Rels (A:Type) : EMonoid equiv (@comp  A) (@id A).
Proof.
 split.
 - apply fun_ext_equiv.  
 - apply comp_proper.
 - unfold comp;intros f g h x;reflexivity.
 - intros f x;reflexivity.
 - intros f x;reflexivity.
Defined.

Definition fibonacci_alt (n:nat) :=
   fst  (Epower (M:= Rels (Z*Z)) (fun p:Z*Z => let (a,b):= p in (b,a+b)) n (1,1)).

Compute fibonacci_alt 40.

Module SemiRing.

(* Overloaded notations *)

Class RingOne A := ring_one : A.
Class RingZero A := ring_zero : A.
Class RingPlus A := ring_plus :> monoid_binop A.
Class RingMult A := ring_mult :> monoid_binop A.

Infix "+" := ring_plus.
Infix "*" := ring_mult.
Notation "0" := ring_zero.
Notation "1" := ring_one.

Typeclasses Transparent RingPlus RingMult RingOne RingZero.

Class Distribute `{Equiv A} (f g: A -> A -> A): Prop :=
  { distribute_l a b c: f a (g b c) == g (f a b) (f a c)
  ; distribute_r a b c: f (g a b) c == g (f a c) (f b c) }.

Class Commutative {A B} `{Equiv B} (m: A -> A -> B): Prop := 
  commutativity x y : m x y = m y x.

Class Absorb {A} `{Equiv A} (m: A -> A -> A) (x : A) : Prop := 
  { absorb_l c : m x c = x ;
    absorb_r c : m c x = x }.

Class ECommutativeMonoid `(Equiv A) (E_dot : monoid_binop A)(E_one : A):=
  { e_commmonoid_monoid :> EMonoid equiv E_dot E_one;
    e_commmonoid_commutative :> Commutative E_dot }.

Class ESemiRing (A:Type) (E_eq :Equiv A) (E_plus : RingPlus A) (E_zero : RingZero A)
            (E_mult : RingMult A) (E_one : RingOne A):=
  { add_monoid :> ECommutativeMonoid equiv ring_plus ring_zero ;
    mul_monoid :> EMonoid equiv ring_mult ring_one ;
    ering_dist :> Distribute ring_mult ring_plus ;
    ering_0_mult :> Absorb ring_mult 0
  }.



Section SemiRingTheory.

  Context `{ESemiRing A}.

  Definition ringtwo := 1 + 1.

  Lemma ringtwomult : forall x : A, ringtwo * x == x + x.
  Proof.
    intros;unfold ringtwo;    rewrite distribute_r.
    now rewrite (E_one_left x).
  Qed.

End SemiRingTheory.

End SemiRing.



(** Monoid of Partial Commutation *)

Require Import Coq.Lists.List  Relation_Operators  Operators_Properties.

Section Partial_Com.

Inductive Act : Set := a | b | c.
 

(** action a commutes with action b *)

Inductive transpose : list Act -> list Act -> Prop :=
 transpose_hd : forall w, transpose(a::b::w) (b::a::w)
|transpose_tl : forall x w u, transpose  w u -> transpose (x::w) (x::u).

Definition commute := clos_refl_sym_trans _ transpose.

Instance Commute_E : Equivalence  commute.
Proof. 
split.
- constructor 2.
- constructor 3;auto.
- econstructor 4;eauto.
Qed.

Instance CE : Equiv (list Act) := commute.

Example ex1 :  (c::a::a::b::nil) == (c::b::a::a::nil).
Proof. 
 constructor 4 with (c::a::b::a::nil).
 - constructor 1.
   constructor 2.
   constructor 2.
   constructor 1.
 - constructor 1.
   right;left.
Qed. 


Instance cons_transpose_Proper (x:Act): Proper (transpose ==> transpose)
                                         (cons x).
Proof.
 intros  l l' H;constructor ;auto.
Defined.

Instance append_transpose_Proper (l:list Act): Proper (transpose ==> transpose)
                                         (app l).
Proof.
 induction l.
 - intros z t Ht;simpl;auto.
 - intros z t Ht;simpl;constructor;auto.
Qed.

Instance append_transpose_Proper_1  : Proper (transpose ==> Logic.eq  ==> transpose)
                                         (@app Act).
Proof.
 intros x y H;induction H;intros z t e;subst t. 
 -  simpl;constructor. 
 -  generalize (IHtranspose z z (refl_equal z)); simpl;constructor;auto.
Qed.

Instance append_commute_Proper_1 : 
Proper (Logic.eq ==> commute  ==> commute)
                                         (@app Act).
Proof.
 intros x y e;subst y;intros z t H;elim H.
 - constructor 1.
  apply append_transpose_Proper;auto.
 -  reflexivity.
 -  constructor 3;auto.
 -  intros x0 y z0;constructor 4 with (x++y);auto.
Qed.


Instance  append_commute_Proper_2 : 
Proper (commute ==> Logic.eq   ==> commute) (@app Act).
Proof.
intros x y H; elim H. 
-  intros x0 y0 H0  z t e; subst t; constructor 1.
   apply append_transpose_Proper_1;auto.
-  intros x0 z t e; subst t;constructor 2;auto.
-   intros x0 y0 H0 H1 z t e;subst t.
    constructor 3.
    apply H1;auto.
-  intros x0 y0 z0 H1 H2 H3 H4 z t e;subst t.
   transitivity (y0 ++ z).
   +  apply H2;reflexivity.
   +  apply H4;reflexivity.
Qed.



Instance append_Proper : Proper (commute ==> commute ==> commute) (@app Act).
Proof.
 intros x y H z t H0; transitivity (y++z).
 - now rewrite H.
 - now rewrite H0.
Qed.

Instance app_op :  monoid_binop (list Act):=  @app Act.

Instance PCom  : EMonoid   commute app_op nil.
Proof. 
 split.
 - apply Commute_E.
 - apply append_Proper.
 - unfold monoid_op;induction x;simpl;auto.
   + reflexivity.
   + intros;simpl;unfold app_op; rewrite app_assoc;reflexivity.
 - unfold monoid_op;simpl;reflexivity. 
 - unfold monoid_op,app_op;intro;rewrite app_nil_r;reflexivity.
Qed.


Example ex2:  Epower  (c::a::a::b::nil) 10 == 
     Epower (Epower  (c::b::a::a::nil) 5)  2.
Proof.
  rewrite ex1, <- Epower_x_mult.
  reflexivity.
Qed.



End Partial_Com.


Require Import ZArithRing.

Section Z_additive.

Local Instance Z_plus_op :  monoid_binop Z | 2:= Zplus.


Instance ZAdd : Monoid   Z_plus_op 0 | 2. 
Proof.
  split;intros;unfold Z_plus_op, monoid_op; simpl;ring.
Defined.

Example Ex2 : (2 * 5)%M = 7. 
Proof. reflexivity. Qed.


Example Ex3 : 2 ** 5 = 10.
Proof. reflexivity. Qed.

Example Ex4 : power  (M:=ZMult) 2 5 = 32.
Proof. reflexivity. Qed.

(* OK, let's remove ZAdd *)
End Z_additive.

Example Ex5 : (2  * 5)%M = 10. 
Proof. reflexivity. Qed.

(** Let us build a new instance with priority 1 *)

Instance Zplus_op : monoid_binop Z | 7 := Zplus.

Instance : Monoid   Zplus_op  0 | 1.
split;intros;  unfold  monoid_op, Zplus_op; simpl; ring. 
Defined.

Example Ex6 : (2 * 5)%M = 7.
Proof. reflexivity. Qed.

(* The least priority level wins *)
