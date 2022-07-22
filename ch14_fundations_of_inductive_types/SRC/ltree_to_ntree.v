Require Export List.
 
Inductive ltree (A : Type) : Type :=
  lnode: A -> list (ltree A) ->  ltree A .
 
Inductive ntree (A : Type) : Type :=
               nnode: A -> nforest A ->  ntree A
with nforest (A : Type) : Type :=
          nnil: nforest A
         | ncons: ntree A -> nforest A ->  nforest A.
 
Scheme
ntree_ind2 := Induction for ntree Sort Prop
   with
   nforest_ind2 := Induction for nforest Sort Prop.
 
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
 
Fixpoint ltree_to_ntree {A : Type} (t : ltree A) {struct t} : ntree A :=
 match t with
 |  lnode _ x l =>
     nnode
      A x
      ((fix
        list_tree_to_nforest (l' : list (ltree A)) : nforest A :=
           match l' with
             nil => nnil A
            | t1 :: tl =>
                ncons A (ltree_to_ntree  t1) (list_tree_to_nforest tl)
           end) l)
 end.

Fixpoint
 ntree_to_ltree {A : Type} (t : ntree A) {struct t} : ltree A :=
    match t with nnode _ x f => lnode A x (nforest_to_list_ltree A f) end
 with
 nforest_to_list_ltree (A : Type) (f : nforest A) {struct f} : list (ltree A) :=
    match f with
      nnil _ => nil
     | ncons _ t f' => ntree_to_ltree  t :: nforest_to_list_ltree A f'
    end.
 
Theorem ltree_o_ntree {A:Type}:
 forall t : ntree A,  ltree_to_ntree  (ntree_to_ltree  t) = t.
Proof. 
 intros  t; elim t   using ntree_ind2
 with ( P0 :=
      fun l =>
      (fix
       list_tree_to_nforest (l' : list (ltree A)) : nforest A :=
          match l' with
            nil  => nnil A
           | t1 :: tl => ncons A (ltree_to_ntree  t1) (list_tree_to_nforest tl)
          end) (nforest_to_list_ltree  _ l) = l ).
- simpl; intros a f IHf; rewrite IHf; trivial.
- simpl; trivial.
- simpl; intros n IHn f IHf; rewrite IHn; rewrite IHf; trivial.
Qed.
 
Theorem ntree_o_ltree {A:Type}:
 forall t : ltree A,  ntree_to_ltree  (ltree_to_ntree  t) = t.
Proof.
  intros  t; elim t   using ltree_ind2
              with ( Q :=
                       fun l =>
                         nforest_to_list_ltree
                           A
                           ((fix
                               list_tree_to_nforest (l' : list (ltree A)) : nforest A :=
                               match l' with
                                   nil => nnil A
                                 | t1 :: tl =>
                                   ncons A (ltree_to_ntree  t1) (list_tree_to_nforest tl)
                               end) l) = l ).
- simpl; intros a l IHl; rewrite IHl; trivial.
- simpl; trivial.
- simpl; intros t' IHt' tl IHtl; rewrite IHt'; rewrite IHtl; trivial.
Qed.
