Require Import Bool ZArith.

Inductive Zbtree : Type :=
|  leaf 
|  bnode (r:Z)(t1 t2: Zbtree).


Definition is_leaf (t: Zbtree) : bool :=
 match t with leaf => true | _ => false end.


Fixpoint size (t: Zbtree) : nat :=
match t with
| leaf => 1
| bnode _ t1 t2 => 1 + size t1 + size t2
end.

Require Export Max.

Fixpoint height (t:Zbtree) : nat :=
match t with 
| leaf => 0
| bnode _ t1 t2 => 1 + max (height t1 ) (height t2)
end.

Fixpoint mirror (t:Zbtree) : Zbtree :=
match t with 
| leaf => leaf
| bnode r t1 t2 => bnode r (mirror t2) (mirror t1)
end.

(** to move elsewhere

Definition height'  (t: Zbtree) : nat :=
 Zbtree_rec _  0 (fun _ t1 ht1 t2 ht2 => 1 + max ht1 ht2) t.
*)

Fixpoint memb (n:Z)(t: Zbtree) : bool :=
match t with
| leaf => false
| bnode r t1 t2 => Z.eqb r n || memb n t1 || memb n t2 
end.


Require Export List.

Fixpoint infix_list (t:Zbtree) : list Z :=
match t with leaf => nil
           | bnode r t1 t2 => infix_list t1 ++ (r :: infix_list t2)
end.

(**
m is strictly greater than every node of t 
*)

Fixpoint strict_majorant (m:Z)(t:Zbtree) : bool :=
match t with leaf => true
           | bnode r t1 t2 => Z.ltb r m &&
                                    strict_majorant m t1 && 
                                    strict_majorant m t2
end.


(**
m is strictly less than every node of t 
*)
Fixpoint strict_minorant (m:Z)(t:Zbtree) : bool :=
match t with leaf => true
           | bnode r t1 t2 => Z.ltb m r &&
                                  strict_minorant m t1 && 
                                  strict_minorant m t2
end.


Fixpoint is_searchtree (t:Zbtree) : bool :=
match t with leaf => true
           | bnode n t1 t2 => strict_minorant n t2 &&
                              strict_majorant n t1  &&
                              is_searchtree t1 &&
                              is_searchtree t2 
end.


Fixpoint memb_in_searchtree (n:Z)(t: Zbtree) : bool :=
match t with 
| leaf => false
| bnode r t1 t2 => 
  match Z.compare n r with
      | Lt => memb_in_searchtree n t1
      | Eq => true
      | Gt => memb_in_searchtree n t2
  end
end.

Fixpoint insert_in_searchtree (n:Z)(t: Zbtree) : Zbtree :=
match t with
| leaf => bnode n leaf leaf
| bnode r t1 t2 =>
  match Z.compare n r with
      | Lt => bnode r (insert_in_searchtree n t1) t2
      | Eq => t
      | Gt => bnode r t1 (insert_in_searchtree n t2)
  end
end. 


Definition list_to_searchtree l :=
List.fold_right insert_in_searchtree leaf l.


Definition weak_sort l := 
  infix_list (list_to_searchtree l).

Compute weak_sort (4::6::9::3::8::nil)%Z.


Definition list_to_searchtree_test l : bool :=
 is_searchtree (list_to_searchtree l).


Compute is_searchtree 
  (bnode  8 
          (bnode 5 (bnode 3 leaf leaf)
                   (bnode 7 leaf leaf))
          (bnode 15 (bnode 10 leaf leaf)
                    (bnode 18 leaf leaf)))%Z.


Compute is_searchtree 
  (bnode  8 
          (bnode 5 (bnode 3 leaf leaf)
                   (bnode 7 leaf leaf))
          (bnode 15 (bnode 16 leaf leaf)
                    (bnode 18 leaf leaf)))%Z.
