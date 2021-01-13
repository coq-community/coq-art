Require Import List.

Definition two_first {A:Type}(l:list A) : list A :=
 match l with a :: b :: l' => a :: b :: nil
            | _ => nil
 end.

(** Tests :


Compute two_first  (true::false::true::nil).

Compute  two_first  (6 * 6::nil).
*)


Fixpoint firsts {A:Type}(n:nat)(l:list A){struct n}: list A :=
   match n,l  with
   | 0, l' => nil
   | S n', nil => nil
   | S n', a::l' => a::firsts  n' l'
  end.

