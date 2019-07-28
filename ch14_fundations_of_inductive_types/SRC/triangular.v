Require Import List.

(** A type for triangular arrays *)


Inductive triangular (A B : Type) :=
| base : B -> triangular A B
| line : B -> triangular A (A * B) -> triangular A B. 

Definition triangle (A: Type) := triangular A A.

Arguments base {A B} _.
Arguments line {A B} _ _.

Example t1 : triangle  nat :=
base 6.

Example t2 : triangle nat :=
  line 5
 (base (1, 1)).

Example t3 :triangle nat  :=
 line 6 
(line (5, 3) 
(line (5, (7, 8)) 
(base (1, (2, (3, 4)))))).



Fixpoint height {A B : Type}(t : triangular A B) : nat :=
  match t with base  _ => 1
             | line  _ m' => 1 + height m'
  end.

Example test1 :  height t3 = 4.
Proof.  reflexivity. Qed.


(** getting the vertical edge  of a triangle *)

Fixpoint left_edge_aux {A B : Type}(m : triangular A B): B * list A :=
match m with base b => (b,nil)
           | line b t' => match left_edge_aux t' with (x,y,l) => (b,(x::l)) end
end.


Definition left_edge {A:Type} (m: triangle A) :=
  match left_edge_aux m with (a,l)=> a::l end.


Example test2 : left_edge t3 = 6::5::5::1::nil.
Proof. reflexivity. Qed.

(* getting the lowest row *)

Fixpoint the_base_aux {A B : Type}(m : triangular A B)(f : B -> list A) :  list A :=
match m with base b => f b
           | line b t' => the_base_aux t' (fun p : A * B => fst p :: f (snd p))
end.

Definition the_base {A:Type} (m: triangle  A) :=
 the_base_aux m (fun a:A => a::nil).

Example test3 : the_base t3 = 1 :: 2 :: 3 :: 4 :: nil.
Proof. reflexivity. Qed.

(** getting the diagonal *)

Fixpoint diagonal {A B : Type}(m : triangular A B) :  list B :=
match m with base b =>  b :: nil
           | line b t' => b :: map snd (diagonal  t')
end.


Example test4 : diagonal  t3 = 6 :: 3 :: 8 :: 4 :: nil.
Proof. reflexivity. Qed.


(** flattening a triangle *)


Fixpoint flatten_aux {A}{B}(f: B -> list A) (m : triangular A B) : list A :=
 match m with base  b => f b
            | line   b m' => f b ++ flatten_aux (fun x=> fst x :: (f (snd x))) m'
 end.


Definition flatten {A:Type} (m : triangle A) : list A :=
flatten_aux (fun a => a::nil) m.

Example test5 : flatten t3 =
                6 :: 5 :: 3 :: 5 :: 7 :: 8 :: 1 :: 2 :: 3 :: 4 :: nil.
Proof. reflexivity. Qed.


(** building a triangle with the same data everywhere *)


Fixpoint uniform_aux {A B : Type}(a:A)(b:B)(n:nat) : triangular A B :=
  match n with 0 => base  b
             | S p => line  b (uniform_aux a (a,b)  p)
 end.

Definition uniform {A:Type}(a:A)(n:nat) : triangle A :=
uniform_aux a a n.

Example test6 : uniform 41 3 =
 line 41
(line (41, 41)
(line (41, (41, 41)) 
(base (41, (41, (41, 41)))))).
Proof. reflexivity. Qed.


(** what does this function compute ? *)

Fixpoint mystery_aux {A B : Type}(f:A->A)(a:A)(b:B)(n:nat) : triangular A B :=
  match n with 0 => base  b
             | S p => line  b (mystery_aux f (f a) (f a, b)   p)
 end.

Definition mystery {A:Type} (f : A -> A)(a:A) (n:nat) : triangle A :=
 mystery_aux f a a n.

