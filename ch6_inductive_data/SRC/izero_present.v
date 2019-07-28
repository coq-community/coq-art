Require Export Bool.
Require Export ZArith.

Open Scope Z_scope.

Inductive Z_inf_branch_tree : Set :=
  Z_inf_leaf : Z_inf_branch_tree
| Z_inf_node : Z->(nat->Z_inf_branch_tree)->Z_inf_branch_tree.

Fixpoint any_true (n:nat)(f:nat->bool){struct n}:bool :=
 match n with
   0%nat => f 0%nat
 | S p => orb (f (S p)) (any_true p f)
 end.

Fixpoint izero_present (n:nat)(t:Z_inf_branch_tree) {struct t} :bool :=
 match t with
 | Z_inf_leaf => false
 | Z_inf_node v f =>
   match v with
   |  0 => true
   | _ => any_true n (fun p => izero_present n (f p))
   end
 end.
