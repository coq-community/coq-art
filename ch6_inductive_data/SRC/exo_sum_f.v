Require Import ZArith.
Require Import Arith.

Open Scope Z_scope.

Fixpoint sum_f (f:nat -> Z) (n:nat)  : Z :=
  match n with
  | O => f O
  | S p => sum_f f p + f n
  end.

Theorem sum_n : forall n:nat, 2 * sum_f Z_of_nat n = 
                              Z_of_nat n * (Z_of_nat n + 1).
Proof.
 induction n as [| p IHp].
 -  reflexivity. 
 -  lazy beta iota zeta delta [sum_f]; fold sum_f.
     rewrite Zmult_plus_distr_r; rewrite IHp.
     rewrite inj_S ; unfold Z.succ ; ring.
Qed.
