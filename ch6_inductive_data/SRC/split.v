Require Import List.


Fixpoint split {A B: Type}(l: list (A * B)) : list A * list B :=
 match l with 
   | nil => (nil, nil)
   | (a,b)::l' => let (l'1,l'2) := split  l' 
                   in (a::l'1, b::l'2)
 end.

Fixpoint combine {A B: Type}(l1 : list A)(l2 :list B): list (A*B):=
  match l1,l2 with 
    | nil,nil => nil
    | (a::l'1), (b::l'2) => (a,b)::(combine  l'1 l'2)
    | _,_  => nil
  end.

Theorem combine_of_split {A B : Type} :
  forall l:list (A*B),
    let (l1,l2) :=  split l
    in combine  l1 l2 = l.
Proof.
  induction l; simpl; auto.
  destruct a, (split l); simpl; congruence. 
Qed.

