(* About integer powers (monomorphic version) *)

Set Implicit Arguments.

Require Import ZArith  Div2  Program.

Open Scope Z_scope.

Fixpoint power (a:Z)(n:nat) :=
  match n with 
             | 0%nat => 1
             | S p =>  a * power a p
  end.


(**  Tests:

Compute power 2 40.
 = 1099511627776
     : Z
*)


Program
Fixpoint binary_power_mult (acc x:Z) (n:nat) {measure n} : Z
  (* acc * (power x n) *) :=
  match n with 
    | 0%nat => acc
    | _ => if Even.even_odd_dec n
           then binary_power_mult acc (x * x) (div2 n)
           else binary_power_mult (acc * x) (x * x) (div2 n)
  end.
 Solve Obligations with program_simpl; intros; apply lt_div2; auto with arith.

Definition binary_power (x:Z)(n:nat) := binary_power_mult 1 x n.

(**  Tests:

Compute bunary_power 2 40.
 = 1099511627776
     : Z
*)

Example Ex1 : binary_power 2 234 = power 2 234.
Proof. reflexivity. Qed.
