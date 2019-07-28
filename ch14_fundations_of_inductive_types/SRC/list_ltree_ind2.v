Require Export List.
 
Inductive ltree (A : Type) : Type :=
  lnode: A -> list (ltree A) ->  ltree A .
 
Section correct_ltree_ind.
Variables (A : Type) (P : ltree A ->  Prop) (Q : list (ltree A) ->  Prop).
Hypotheses
   (H : forall (a : A) (l : list (ltree A)), Q l ->  P (lnode A a l))
   (H0 : Q nil)
   (H1 : forall (t : ltree A),
         P t -> forall (l : list (ltree A)), Q l ->  Q (cons t l)).
 
Fixpoint ltree_ind2 (t : ltree A) : P t :=
 match t as x return P x with
    lnode _ a l =>
      H a l ((fix l_ind (l' : list (ltree A)) : Q l' :=
                     match l' as x return Q x with
                        nil => H0
                       | cons t1 tl => H1 t1 (ltree_ind2 t1) tl (l_ind tl)
                     end) l)
 end.
 
End correct_ltree_ind.
 
Section correct_list_ltree_ind.
Variables (A : Type) (P : ltree A ->  Prop) (Q : list (ltree A) ->  Prop).
Hypotheses
   (H : forall (a : A) (l : list (ltree A)), Q l ->  P (lnode A a l))
   (H0 : Q nil)
   (H1 : forall (t : ltree A),
         P t -> forall (l : list (ltree A)), Q l ->  Q (cons t l)).
 
Fixpoint list_ltree_ind2 (l : list (ltree A)) : Q l :=
 match l as x return Q x with
   | nil => H0
   | t :: tl => H1 t (ltree_ind2 A P Q H H0 H1 t) tl (list_ltree_ind2 tl)
 end.
 
End correct_list_ltree_ind.
