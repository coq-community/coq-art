Require Export List.
 
Inductive ltree (A : Type) : Type :=
  lnode: A -> list (ltree A) ->  ltree A .
 
Section define_iter_list.
Variables (A B : Type) (f : A ->  B) (op : B -> B ->  B) (e : B).
 
Fixpoint iter_list (l : list A) : B :=
 match l with   nil => e
               | a :: tl => op (f a) (iter_list tl) end.
 
End define_iter_list.
Arguments iter_list [A B]. 

(* It is hard to explain, but if we define iter_list outside a section
  then the following definition is not accepted. *)
 
Fixpoint lcount (A : Type) (t : ltree A) {struct t} : nat :=
 match t with lnode _ a l => iter_list (lcount A) plus 1 l end.

(* Here is an alternative definition of iter_list that cannot
   be used to define lcount by replacing iter_list with iter_list'.
   It is a well-known property of guarded definitions for structural
   recursion that objects with the same type cannot be interchanged.
   Here the function cannot be used because recursive calls to
   iter_list' contain instances of f that are not applied to arguments.
   It is thus impossible to check whether these instances satisfy a
   structural guard condition. *)
 
Fixpoint iter_list' (A B : Type) (f : A ->  B) (op : B -> B ->  B) (e : B)
                    (l : list A) {struct l} : B :=
 match l with
   nil => e
  | a :: tl => op (f a) (iter_list' A B f op e tl)
 end.
Arguments iter_list' [A B].