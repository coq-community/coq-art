
Require Export ZArith  List  Arith Bool.

(* 
 
Inductive month : Set :=
| January : month | February : month | March : month
| April : month   | May : month      | June : month
| July : month    | August : month   | September : month
| October : month | November : month | December : month.

*)

(** short form 
*)
Inductive month : Set :=
| January | February | March     | April   | May      | June 
| July    | August   | September | October | November | December.

(** Tests :

Check month_ind.

Check month_rec.
*)


Theorem month_equal :
forall m:month, 
 m=January \/ m=February \/ m=March \/ m=April \/ m=May \/ m=June \/
 m=July \/ m=August \/  m=September \/ m=October \/ m=November \/
 m=December.
Proof.  
 destruct m; auto 12.
Qed.

(** explicit use of maont_ind:

*)
Theorem month_equal' :
forall m:month, 
 m=January \/ m=February \/ m=March \/ m=April \/
 m=May \/ m=June \/ m=July \/ m=August \/ 
 m=September \/ m=October \/ m=November \/ m=December.
Proof.  
 intro m; pattern m; apply month_ind; auto 12.
Qed.



Definition month_length (leap:bool)(m:month) : nat :=
  match m with
  | January => 31 | February => if leap then 29 else 28
  | March => 31   | April => 30    | May => 31  | June => 30 
  | July => 31    | August => 31   | September => 30  
  | October => 31 | November => 30 | December => 31
  end.

Definition month_length' (leap:bool) :=
  month_rec (fun m:month => nat)
  31 (if leap then 29 else 28) 31 30 31 30 31 31 30 31 30 31.


Definition month_length'' (leap:bool)(m:month) :=
 match m with
 | February => if leap then 29 else 28
 | April  | June  | September | November => 30
 | _  => 31
 end.

(** Tests :

Compute  (fun leap => month_length leap November).
*)

Example  length_february : month_length false February = 28.
Proof. reflexivity. Qed.

(* Definition with Record *)

Record plane : Set := point {abscissa : Z; ordinate : Z}.

Definition in_diagonal (p:plane) :=
  Z_eq_bool (abscissa p) (ordinate p).


Inductive vehicle : Set :=
  bicycle : nat->vehicle | motorized : nat->nat->vehicle.

(** 
Check vehicle_ind.
*)

Definition nb_wheels (v:vehicle) : nat :=
  match v with
  | bicycle x => 2
  | motorized x n => n
  end.

Definition nb_seats (v:vehicle) : nat :=
  match v with
  | bicycle x => x
  | motorized x _ => x
  end.

Theorem at_least_28 :
 forall (leap:bool)(m:month), 28 <= month_length leap m.
Proof.
 intros leap m; case m; simpl; auto with arith.
 case leap; simpl; auto with arith.
Qed.

Definition next_month (m:month) :=
  match m with
  |  January => February  | February => March | March => April
  | April => May         | May => June       | June => July
  | July => August       | August => September
  | September => October | October => November
  | November => December | December => January
  end.

Theorem next_august_then_july :
 forall m:month, next_month m = August -> m = July.
Proof.
 intros m; case m; simpl; intros Hnext_eq;
    (reflexivity || discriminate Hnext_eq).
Qed.
 


(* Simulating discriminate (just for the fun) *)

Theorem not_January_eq_February' : January <> February.
Proof.
 unfold not; intros H. 
 change ((fun m:month =>
          match m with | January => True | _ => False end)
        February).
 rewrite <- H.
 trivial.
Qed.

(* Using injection *)

Theorem bicycle_eq_seats :
 forall x1 y1:nat, bicycle x1 = bicycle y1 -> x1 = y1.
Proof.
 intros x1 y1 H.
 injection H.
 trivial.
Qed.

(* Simulating injection (for the fun) *)

Theorem bicycle_eq_seats' :
 forall x1 y1:nat, bicycle x1 = bicycle y1 -> x1 = y1.
Proof.
 intros x1 y1 H.
 change (nb_seats (bicycle x1) = nb_seats (bicycle y1)).
 rewrite H; reflexivity.
Qed.

Theorem next_march_shorter :
 forall (leap:bool)(m1 m2:month), next_month m1 = March ->
   month_length leap m1 <= month_length leap m2.
Proof.
 intros leap m1 m2 H.
 case_eq m1; try  (intro H0; rewrite H0 in H; simpl in H; discriminate H).
  case leap ; case m2 ; simpl; auto with arith.
Qed.

(* A first, detailed, proof of associativity of + *)

Theorem plus_assoc :
 forall x y z:nat, (x+y)+z = x+(y+z).
Proof.
 induction x as [ | x0 IHx0].
 -  simpl; reflexivity.
 - simpl; intros y z; rewrite IHx0; reflexivity.
Qed.


Fixpoint mult2 (n:nat) : nat :=
   match n with 
   | 0 => 0
   | S p => S (S (mult2 p))
   end.

Inductive Z_btree : Set :=
  Z_leaf : Z_btree | Z_bnode : Z->Z_btree->Z_btree->Z_btree.

Fixpoint sum_all_values (t:Z_btree) : Z :=
  (match t with
   | Z_leaf => 0
   | Z_bnode v t1 t2 =>
       v + sum_all_values t1 + sum_all_values t2
  end)%Z.
 
Fixpoint zero_present (t:Z_btree) : bool :=
   match t with
   | Z_leaf => false
   | Z_bnode (0%Z)  t1 t2 => true
   | Z_bnode _ t1 t2 =>
        zero_present t1 ||  zero_present t2
   end.

Fixpoint add_one (x:positive) : positive :=
  match x with
  | xI x' => xO (add_one x')
  | xO x' => xI x'
  | xH => 2%positive
  end.


Inductive Z_fbtree : Set :=
  Z_fleaf : Z_fbtree | Z_fnode : Z ->(bool->Z_fbtree)-> Z_fbtree.

Definition right_son (t:Z_btree) : Z_btree :=
  match t with
  | Z_leaf => Z_leaf
  | Z_bnode a t1 t2 => t2
  end.


Definition fright_son (t:Z_fbtree) : Z_fbtree :=
  match t with
  | Z_fleaf => Z_fleaf
  | Z_fnode a f => f false
  end.

(**

Check Z_fbtree_ind. 
*)

Fixpoint fsum_all_values (t:Z_fbtree) : Z :=
 (match t with
  | Z_fleaf => 0
  | Z_fnode v f =>
     v + fsum_all_values (f true) + fsum_all_values (f false)
  end )%Z .

Inductive Z_inf_branch_tree : Set :=
| Z_inf_leaf : Z_inf_branch_tree
| Z_inf_node : Z->(nat->Z_inf_branch_tree)->Z_inf_branch_tree.


Fixpoint sum_f (n:nat)(f : nat -> Z) : Z
 := (match n with 
       | O => 0
       | S p => f n + sum_f p f
     end)%Z.

Fixpoint n_sum_all_values (n:nat)(t:Z_inf_branch_tree) : Z :=
  (match t with
    | Z_inf_leaf => 0
    | Z_inf_node v f =>
         v + sum_f n (fun x:nat => n_sum_all_values n (f x))
    end )%Z.



Definition mult2' : nat->nat :=
  fix f (n:nat) : nat :=
    match n with 0 => 0 | S p => S (S (f p)) end.



Fixpoint app {A:Type}(l m:list A) : list A :=
  match l with
  | nil => m
  | cons a l1 => cons a (app  l1 m)
  end.


Definition pred_option (n:nat) : option nat :=
  match n with O => None | S p => Some p end.

Definition pred2_option (n:nat) : option nat :=
  match pred_option n with
  | None => None
  | Some p => pred_option p
  end.

Fixpoint nth_option {A:Type} (n:nat)(l:list A) : option A :=
  match n, l with
  | O, cons a tl => Some a
  | S p, cons a tl => nth_option  p tl
  | _, nil => None
  end.

(** Some tests: 

Print fst.

Check (sum nat bool). 

Check (inl bool 4).

Check (inr nat false).
*)


Inductive ltree (n:nat) : Set :=
  | lleaf : ltree n
  | lnode : forall p:nat, p <= n -> ltree n -> ltree n -> ltree n.


Inductive sqrt_data (n:nat) : Set :=
  sqrt_intro : forall x:nat, x*x <= n -> n <  S x * S x -> sqrt_data n.

Inductive htree (A:Type) : nat->Type :=
  | hleaf : A->htree A 0
  | hnode : forall n:nat, A -> htree A n -> htree A n -> htree A (S n).

(**

Check htree_ind.

*)


Fixpoint htree_to_btree (n:nat)(t:htree Z n){struct t} : Z_btree :=
  match t with
  | hleaf _ x => Z_bnode x Z_leaf Z_leaf
  | hnode _ p v t1 t2 =>
      Z_bnode v (htree_to_btree p t1)(htree_to_btree p t2)
  end.

Fixpoint invert (A:Type)(n:nat)(t:htree A n){struct t} : htree A n :=
  match t in htree _ x return htree A x with
  | hleaf _ v => hleaf A v
  | hnode _ p v t1 t2 => hnode A p v (invert A p t2)(invert A p t1)
  end.

(**

Print Empty_set.

Check Empty_set_ind. 
*)

Inductive strange : Set :=  cs : strange->strange.


Theorem strange_empty : forall x:strange, False.
Proof.
 intro x; induction x.
 assumption.
Qed.

(** attempt to prove falsehood

Theorem nat_not_strange :  forall n:nat, False.
Proof.
 intros x; elim x.
Abort.

*)

Inductive even_line : nat->Set :=
  | even_empty_line : even_line 0
  | even_step_line : forall n:nat, even_line n -> even_line (S (S n)).

(** Tests :

Check even_empty_line.

Check (even_step_line _ even_empty_line). 


Check (even_step_line _ (even_step_line _ even_empty_line)). 
*)

