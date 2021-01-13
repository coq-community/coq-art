
Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export Omega.
Require Export Zwf.
Require Export Relations.
Require Export Inverse_Image.

 (**
 Binary trees labeleld with integers

*)
Inductive Z_btree : Set :=
| Z_leaf : Z_btree
| Z_bnode : Z->Z_btree->Z_btree->Z_btree.

(**

Have a look at the  induction principles

Print Z_btree_ind.
Print Z_btree_rect.
 *)


(**
  Another definition : A binary node's sons are represented
 through a function.
*)
Inductive Z_fbtree : Set :=
  Z_fleaf : Z_fbtree
| Z_fnode : Z->(bool->Z_fbtree)->Z_fbtree.

(** even natural numbers *)

Inductive even : nat->Prop :=
  | O_even : even 0%nat
  | plus_2_even : forall n:nat, even n -> even (S (S n)).


Open Scope nat_scope. 

(** perfect  binary trees (indexed by their height) 
*)

Inductive htree (A:Set) : nat->Set :=
  hleaf : A -> htree A 0
| hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).

(** infinitely branching trees *)

Inductive inf_branch_tree (A:Set) : Set :=
  inf_leaf : inf_branch_tree A
| inf_node : A -> (nat -> inf_branch_tree A) -> inf_branch_tree A.

(** For compatibility with the book :
    have a look at Tpe Classes ! 
*)

Record group : Type := 
  {A : Type;
   op : A->A->A;
   sym : A->A;
   e : A;
   e_neutral_left : forall x:A, op e x = x;
   sym_op : forall x:A, op (sym x) x = e;
   op_assoc : forall x y z:A, op (op x y) z = op x (op y z);
   op_comm : forall x y:A, op x y = op y x}.  


Fixpoint nat_simple_rec (A:Type)(exp1:A)(exp2:nat->A->A)(x:nat)
  : A :=
  match x with
  | O => exp1
  | S p => exp2 p (nat_simple_rec A exp1 exp2 p)
  end.

Definition example_codomain (b:bool) : Set :=
  match b with true => nat | false => bool end.

Definition example_dep_function (b:bool) : example_codomain b :=
  match b as x return example_codomain x with
  | true => 0
  | false => true
  end.

Inductive type_name (A B:Type) : nat -> nat -> Type := .

Definition bool_case
   (F:bool -> Type)(v1:F true)(v2:F false)(x:bool) :=
  match x return F x with true => v1 | false => v2 end.   

Module redefine_nat_case.

Definition nat_case
  (F:nat -> Type)(exp1:F 0)(exp2:forall p:nat, F (S p))(n:nat) :=
  match n as x return F x with
  | O => exp1
  | S p => exp2 p
  end.

End redefine_nat_case.


Module Type nat_rect_type.
Parameter
nat_rect :
  forall f:nat->Type, f 0 ->(forall n:nat, f n -> f (S n))-> forall n:nat, f n.
End nat_rect_type.

Module nat_rect_module : nat_rect_type.

Fixpoint nat_rect (f:nat->Type)(exp1:f 0)
 (exp2:forall p:nat, f p -> f (S p))(n:nat){struct n} : f n :=
  match n as x return f x with
  | O => exp1
  | S p => exp2 p (nat_rect f exp1 exp2 p)
  end.

End nat_rect_module.

Definition mult2' :=
  nat_rect (fun n:nat => nat) 0 (fun p v:nat => S (S v)).

Module redefine_nat_ind.

Fixpoint nat_ind (P:nat->Prop)(exp1:P 0)
 (exp2:forall p:nat, P p -> P (S p))(n:nat){struct n} : P n :=
  match n as x return P x with
  | O => exp1
  | S p => exp2 p (nat_ind P exp1 exp2 p)
  end.

End redefine_nat_ind.


Module Type Z_btree_rect_type.
Parameter 
Z_btree_rect :
  forall f:Z_btree->Type,
   f Z_leaf ->
   (forall (n:Z)(t1:Z_btree), f t1 ->
      forall t2:Z_btree, f t2 -> f (Z_bnode n t1 t2))->
   forall t:Z_btree, f t.
End Z_btree_rect_type.

Module Z_btree_rect_module : Z_btree_rect_type.

Fixpoint Z_btree_rect (f:Z_btree->Type)(exp1:f Z_leaf)
 (exp2:forall (n:Z)(t1:Z_btree), f t1 ->
        forall t2:Z_btree, f t2 -> f (Z_bnode n t1 t2))
 (t:Z_btree) : f t :=
  match t as x return f x with
  | Z_leaf => exp1
  | Z_bnode n t1 t2 =>
      exp2 n t1 (Z_btree_rect f exp1 exp2 t1) t2
        (Z_btree_rect f exp1 exp2 t2)
  end.

End Z_btree_rect_module.

Scheme le_ind' := Induction for le Sort Prop.

(** 

Compute
  (forall (n:nat)(P:nat->Prop),
     (fun (n':nat)(P:forall m:nat, n' <= m -> Prop) =>
        P n' (le_n n')->
        (forall (m:nat)(h:n' <= m), P m h -> P (S m)(le_S n' m h))->
        forall (m:nat)(h:n' <= m), P m h) n
       (fun (m:nat)(_:n <= m) => P m)).
*)

Fixpoint even_ind_max (P:forall n:nat, even n -> Prop)
 (exp1:P 0 O_even)
 (exp2:forall (n:nat)(t:even n),
         P n t -> P (S (S n))(plus_2_even n t))(n:nat)(t:even n)
 {struct t} : P n t :=
  match t as x0 in (even x) return P x x0 with
  | O_even => exp1
  | plus_2_even p t' => exp2 p t' (even_ind_max P exp1 exp2 p t')
  end.

Fixpoint even_ind' (P:nat->Prop)(exp1:P 0)
 (exp2:forall n:nat, even n -> P n -> P (S (S n)))(n:nat)(t:even n)
 {struct t} : P n :=
  match t in (even x) return P x with
  | O_even => exp1
  | plus_2_even p t' => exp2 p t' (even_ind' P exp1 exp2 p t')
  end.


Definition clos_trans_ind' (A:Set)(R P:A->A->Prop)
 (exp1:forall x y:A, R x y -> P x y)
 (exp2:forall x y z:A,
         clos_trans A R x y ->
         P x y -> clos_trans A R y z -> P y z -> P x z)(x y:A)
 (p:clos_trans A R x y) : P x y.
Proof.
 induction p.
 -  intros;apply exp1;auto.
 -  intros;eapply exp2;eauto.
Defined.



Fixpoint clos_trans_ind'' (A:Set)(R P:A->A->Prop)
 (exp1:forall x y:A, R x y -> P x y)
 (exp2:forall x y z:A,
         clos_trans A R x y ->
         P x y -> clos_trans A R y z -> P y z -> P x z)(x y:A)
 (p:clos_trans A R x y){struct p} : P x y :=
 match p in (clos_trans _ _ _ x0) return P x x0 with
 | t_step  _ _ _ y' h => exp1 x y' h
 | t_trans _ _ _ y' z' h1 h2 =>
   exp2 x y' z' h1 (clos_trans_ind'' A R P exp1 exp2  x y' h1) h2
     (clos_trans_ind'' A R P exp1 exp2  y' z' h2)
  end.

Module even_ind_max_redefined. 

 Scheme even_ind_max := Induction for even Sort Prop.

End even_ind_max_redefined. 

Module nat_simple_rec_redefined.

Scheme nat_simple_rec := Minimality for nat Sort Set.

End nat_simple_rec_redefined. 

Definition rich_minus (n m:nat) := {x : nat | x+m = n}.

Definition le_rich_minus : forall m n:nat, n <= m -> rich_minus m n.
 induction m as [ | n IHn].
 -  intros n Hle; exists 0.
    now  inversion Hle.
 -  intros p; case p.
     + intro Hle; exists (S n); auto with arith.
     + intros q Hle; case (IHn q).
       * inversion Hle;auto with arith.
       * intros x Hx; exists x; rewrite <- Hx; auto with arith.
Defined.

Inductive lfactor {A: Type} : list A -> list A -> Prop :=
  lf1 : forall u:list A, lfactor nil u
| lf2 : forall (a:A)(u v:list A),
       lfactor u v -> lfactor (cons a u)(cons a v). 


Module redefine_eq_rec.

Definition eq_rect (A:Type)(x:A)(P:A->Type)(f:P x)(y:A)(e:x = y)
  : P y := match e in (_ = x) return P x with
           | refl_equal => f
           end.

Definition eq_rec {A:Type}(x:A)(P:A->Set) :
  P x -> forall y:A, x = y -> P y := eq_rect A x P.

End redefine_eq_rec.

Section update_def.
  Variables (A : Type)(A_eq_dec : forall x y:A, {x = y}+{x <> y}).
  Variables (B : A -> Type)(a : A)(v : B a)(f : forall x:A, B x).

  Definition update (x:A) : B x :=
    match A_eq_dec a x with
    | left h => eq_rect a B v x h
    | right h' => f x
    end.

End update_def.

(** 
Check (fun eq_rect_eq
     :forall (U:Type)(p:U)(Q:U->Set)(x:Q p)(h:p = p),
                 x = eq_rec p Q x p h =>  False).

Check (fun update_eq
     :forall (A:Type)(eq_dec:forall x y:A, {x = y}+{x <> y})
                 (B:A->Type)(a:A)(v:B a)(f:forall x:A, B x),
                 update A eq_dec B a v f a = v =>  False).
*)

Inductive ntree (A:Type) : Type :=
  nnode : A -> nforest A -> ntree A
with nforest (A:Type) : Type :=
  nnil : nforest A | ncons : ntree A -> nforest A -> nforest A.
Open Scope Z_scope.

Fixpoint count (A:Type)(t:ntree A){struct t} : Z :=
  match t with
  | nnode _ a l => 1 + count_list A l
  end
 with count_list (A:Type)(l:nforest A){struct l} : Z :=
  match l with
  | nnil _ => 0
  | ncons _ t tl => count A t + count_list A tl
  end.

Module Type ntree_ind_type.

Parameter 
ntree_ind :
  forall (A:Type)(P:ntree A -> Prop),
    (forall (a:A)(l:nforest A), P (nnode A a l))->
    forall t:ntree A, P t.

End ntree_ind_type.

Module ntree_ind_module.
Definition ntree_ind := ntree_ind.
End ntree_ind_module.

(**

Print ntree_ind_module.ntree_ind.
*)

Scheme ntree_ind2 :=
   Induction for ntree Sort Prop
 with nforest_ind2 :=
   Induction for nforest Sort Prop.

Inductive occurs (A:Type)(a:A) : ntree A -> Prop :=
| occurs_root : forall l, occurs A a (nnode A a l)
| occurs_branches :
   forall b l, occurs_forest A a l -> occurs A a (nnode A b l)
with occurs_forest (A:Type)(a:A) : nforest A -> Prop :=
  occurs_head :
   forall t tl, occurs A a t -> occurs_forest A a (ncons A t tl)
| occurs_tail :
   forall t tl, 
    occurs_forest A a tl -> occurs_forest A a (ncons A t tl).

Fixpoint n_sum_values (t:ntree Z) : Z :=
  match t with
  | nnode _ z l => z + n_sum_values_l l
  end
 with n_sum_values_l (l:nforest Z) : Z :=
  match l with
  | nnil _ => 0
  | ncons _ t tl => n_sum_values t + n_sum_values_l tl
  end.

#[export] Hint Resolve occurs_branches occurs_root Zplus_le_compat : core.

Theorem greater_values_sum :
 forall t:ntree Z,
   (forall x:Z, occurs Z x t -> 1 <= x)-> count Z t <= n_sum_values t.
Proof.
 intros t; elim t using ntree_ind2 with
  (P0 := fun l:nforest Z =>
           (forall x:Z, occurs_forest Z x l -> 1 <= x)->
           count_list Z l <= n_sum_values_l l).
 -  intros z l Hl Hocc; lazy beta iota delta -[Zplus Z.le];
    fold count_list n_sum_values_l;   auto with *.
 
 -  auto with zarith.
 -  intros t1 Hrec1 tl Hrec2 Hocc; lazy beta iota delta -[Zplus Z.le];
  fold count count_list n_sum_values n_sum_values_l.
  apply Zplus_le_compat.
  apply Hrec1; intros; apply Hocc; apply occurs_head; auto.
  apply Hrec2; intros; apply Hocc; apply occurs_tail; auto.
Qed.

Inductive ltree (A:Type) : Type :=
    lnode : A -> list (ltree A)-> ltree A.

Section correct_ltree_ind.

Variables
  (A : Type)(P : ltree A -> Prop)(Q : list (ltree A)-> Prop).

Hypotheses
 (H : forall (a:A)(l:list (ltree A)), Q l -> P (lnode A a l))
 (H0 : Q nil)
 (H1 : forall t:ltree A, P t -> forall l:list (ltree A), Q l -> Q (cons t l)).


Fixpoint ltree_ind2 (t:ltree A) : P t :=
  match t as x return P x with
  | lnode _ a l =>
      H a l
        (((fix l_ind (l':list (ltree A)) : Q l' :=
             match l' as x return Q x with
             | nil => H0
             | cons t1 tl => H1 t1 (ltree_ind2 t1) tl (l_ind tl)
             end)) l)
  end.

End correct_ltree_ind.



