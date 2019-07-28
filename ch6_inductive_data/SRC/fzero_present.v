Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.

Inductive Z_fbtree : Set :=
 | Z_fleaf 
 | Z_fnode (root : Z)(f : bool -> Z_fbtree).


Fixpoint fzero_present (t:Z_fbtree) : bool :=
 match t with
  | Z_fleaf => false
  | Z_fnode v f => match v with 0 => true
                              | _ => fzero_present (f true) ||
                                     fzero_present (f false)
                   end
 end.

