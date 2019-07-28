(* We want a dependently typed recursive function.  The output type is itself
  described by a recursive function. *)

Fixpoint bool_nat_type (n:nat) : Set :=
  match n with 0 => nat | 1 => bool | S (S n) => bool_nat_type n end.

(* The difficult point is to describe the computation at each
   recursive step, knowing that sometimes this computation deals with
   boolean values, while at other times it deals with integer
   values.  The trick is to discover that computations can actually
   always be described by the same function as for the
   pre-predecessor.

   A dependently typed pattern-matching construct is need. *)

Require Import Bool.

Fixpoint bool_nat_fun_aux (n:nat) :  bool_nat_type n -> bool_nat_type n :=
 match n return bool_nat_type n -> bool_nat_type n with
   0 => S | 1 => negb | S (S n) => bool_nat_fun_aux n
 end.


(* The function is then easy to describe.  We can use "Compute"
   to check that its value is always as required. *)
 
Fixpoint bool_nat_fun (n:nat) : bool_nat_type n :=
 match n return bool_nat_type n with
   0 => 0 
 | 1 => true
 | S (S n) => bool_nat_fun_aux n (bool_nat_fun n)
 end.

(** Tests :

Compute (bool_nat_fun 6).

Compute (bool_nat_fun 7).

Compute (bool_nat_fun 9).

Compute (bool_nat_fun 7 : bool).

Compute (bool_nat_fun 6 : nat).

*)



(* Defining a function of this form was fun, but will it ever be
   useful? *)

