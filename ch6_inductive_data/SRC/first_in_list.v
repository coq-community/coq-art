Require Export List.

Fixpoint first_in_list {A:Type} (p:A->bool)(l:list A) : option A :=
  match l with
    nil => None
  | a::tl =>
     match p a with
       true => Some a
     | false => first_in_list  p tl
     end
  end.
