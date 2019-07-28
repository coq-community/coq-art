Require Import Arith List Bool.

(* EXAMPLES *) 

(* The following function takes two arguments a and b
which are numbers of type nat and returns b + 2 * (a + b) *)
Definition f_ex (a b : nat) := b + 2 * (a + b).

(* When p is a pair, you can access its components by the "pattern-matching"
  construct illustrated in the following function. *)

Definition add_pair_components (p : nat * nat) :=
  match p with (a, b) => a + b end.

(* f_ex is a function with two arguments.  add_pair_components is a
  function with one argument, which is a pair. *)

(* END OF EXAMPLES *)

(* 1/ Define a function that takes two numbers as arguments and returns
  the sum of the squares of these numbers. *)

Definition f1_1 (x y : nat) : nat := x * x + y * y.

(* 2/ Define a function that takes 5 arguments a b c d e, which are all
   numbers and returns the sum of all these numbers. *)

Definition f1_2 (a b c d e : nat) := a + b + c + d + e.

(* 3/ Define a function named add5 that takes a number as argument and returns
   this number plus 5. *)

Definition add5 (x : nat) := x + 5.

(* The following should return 8 *)
Compute add5 3.

(* The following commands make it possible to find pre-defined functions *)


(* 4/ Write a function swap of type list nat -> list nat such that
  swap (a::b::l) = (b::a::l)  and
  swap l' = l' if l' has less than 2 elements. *)

Definition swap (l : list nat) : list nat :=
 match l with
   a::b::l => b::a::l
 | _ => l
 end.

(* 5/ Write a function proc2 of type list nat -> nat, such that
   proc2 (a::b::l) = (b + 3) and
   proc2 l' = 0 if l' has less than 2 elements.

   In other words, proc2 only processes the 2nd argument of the list and
   returns that number plus 3.  If there is no second argument to the list,
   proc2 returns 0.  *)

Definition proc2 (l : list nat) : nat :=
  match l with
    a::b::l => b + 3
  | _ => 0
  end.

(* 6/ Write a function ms of type list nat -> list nat such that
      ms (a::b::...::nil) = a+2::b+2::...::nil
      For instance
      ms (2::3::5::nil) = (4::5::7::nil) *) 

Fixpoint ms (l : list nat) : list nat :=
  match l with
    a::l' => a + 2 :: ms l'
  | nil => nil
  end.

(* 7/ Write a function sorted of type list nat -> bool, such that
    sorted l = true exactly when the natural numbers in
   l are in increasing order. *)
Locate leb.
Fixpoint sorted (l : list nat) : bool :=
  match l with
    a::l' =>
    match l' with b::_ =>
                  if Nat.leb a b then sorted l' else false | _ => true end
  | nil => true
  end.

(* 8/ Write a function p2 of type nat -> nat such that 
    p2 n = 2 ^ n *)

Fixpoint p2 (n : nat) :=
  match n with 0 => 1 | S p => 2 * p2 p end.

(* 9/ Write a function salt of type nat -> nat -> nat such that
   salt x n = x ^ n - x^ (n-1) + x^(n-2) .... + 1 or -1, if x <> 0,
   depending on the parity of n, thus
   salt x 3 = x^3 - x^2 + x - 1
   salt x 4 = x^4 - x^3 + x^2 - x + 1
   salt 2 3 = 5

   You may have to define auxiliary functions. *)

Fixpoint even n :=
  match n with 0 => true | 1 => false | S (S p) => even p end.

Fixpoint salt (x n : nat) :=
  match n with
    0 => 1
  | S p => if even n then x * salt x p + 1 else x * salt x p - 1
  end.



Fixpoint pow x n :=
  match n with 0 => 1 | S p => x * pow x p end.

