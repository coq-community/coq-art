Require Import Vector.

(** A type for triangular arrays *)


Inductive triangular (A B : Type) : nat -> Type:=
| base : B -> triangular  A B 0
| line : forall n,  B -> triangular  A (A * B) n -> triangular  A B (S n). 

Definition triangle (A: Type) n := triangular A A n.

Arguments base {A B} _.
Arguments line {A B n} _ _.

Example t1 : triangle  nat 0 :=
base 6.

Example t2 : triangle nat 1:=
  line 5
 (base (1, 1)).

Example t3 :triangle nat 3 :=
 line 6 
(line (5, 3) 
(line (5, (7, 8)) 
(base (1, (2, (3, 4)))))).



(** getting the vertical edge  of a triangle *)

Fixpoint left_edge_aux {A B : Type}n (m : triangular A B n): B * t  A  n:=
match m with base b => (b,@nil A )
           | @line _ _ p b t' => match left_edge_aux p t' with (x,y,l) => (b,(cons A x _ l)) end
end.


Definition left_edge {A:Type} {n} (m: triangle A n) :=
  match left_edge_aux n m with (a,l)=> cons _ a _ l end.

Compute left_edge t3.

(** To complete ... *)
