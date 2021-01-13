(* binary search trees on Z *)
(* (C) Pierre Castéran *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Export ZArith.
Open Scope Z_scope.

(* binary trees *)

Inductive Z_btree : Set :=
  | Z_leaf : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Definition is_bnode (t: Z_btree) : Prop :=
 match t with Z_leaf => False | _ => True end.


(* n : Z occurs in some tree *)
Inductive occ (n:Z) : Z_btree -> Prop :=
  | occ_root : forall t1 t2:Z_btree, occ n (Z_bnode n t1 t2)
  | occ_l : forall (p:Z) (t1 t2:Z_btree), occ n t1 -> occ n (Z_bnode p t1 t2)
  | occ_r : forall (p:Z) (t1 t2:Z_btree), occ n t2 -> occ n (Z_bnode p t1 t2)
 .

#[ export ] Hint Resolve occ_root occ_l occ_r: searchtrees.

Derive Inversion_clear OCC_INV with
 (forall (z z':Z) (t1 t2:Z_btree), occ z' (Z_bnode z t1 t2)).



Lemma occ_inv :
 forall (z z':Z) (t1 t2:Z_btree),
   occ z' (Z_bnode z t1 t2) -> z = z' \/ occ z' t1 \/ occ z' t2.
Proof.
 intros z z' t1 t2 H.
 inversion H using OCC_INV; auto with searchtrees.
Qed.

#[ export ] Hint Resolve occ_inv: searchtrees.

Lemma not_occ_Leaf : forall z:Z, ~ occ z Z_leaf.
Proof.
 unfold not; intros z H; inversion_clear H.
Qed.

#[ export ] Hint Resolve not_occ_Leaf: searchtrees.


(* auxiliary definitions for search, insertion and deletion *)

(* z is less than every label in t *)
Inductive min (z:Z) (t:Z_btree) : Prop :=
    min_intro : (forall z':Z, occ z' t -> z < z') -> min z t.

#[ export ] Hint Resolve min_intro: searchtrees.

(* z is greater than every label in t *)
Inductive maj (z:Z) (t:Z_btree) : Prop :=
    maj_intro : (forall z':Z, occ z' t -> z' < z) -> maj z t
 .

#[ export ] Hint Resolve maj_intro: searchtrees.

(* search-ness predcate on binary trees *)

Inductive search_tree : Z_btree -> Prop :=
  | leaf_search_tree : search_tree Z_leaf
  | bnode_search_tree :
      forall (z:Z) (t1 t2:Z_btree),
        search_tree t1 ->
        search_tree t2 ->
        maj z t1 -> min z t2 -> search_tree (Z_bnode z t1 t2)
 .

(** certified binary search-trees *)

Definition sch_tree : Set := sig search_tree.

Definition sch_occ (p : Z) (s : sch_tree) :=
   match s with exist _ t _ => occ p t end.

Definition sch_occ_dec_spec (p:Z) (s:sch_tree) :=
               {sch_occ p s} + {~ sch_occ p s}.


Inductive sch_INSERT (n:Z) (t t':sch_tree) : Prop :=
    sch_insert_intro :
      (forall p:Z, sch_occ p t -> sch_occ p t') ->
      sch_occ n t' ->
      (forall p:Z, sch_occ p t' -> sch_occ p t \/ n = p) ->
       sch_INSERT n t t'.

Definition sch_insert_spec (n:Z) (t:sch_tree) : Set :=
       {t' : sch_tree | sch_INSERT n t t'}.

Require Import List.

Definition sch_list2tree_spec (l:list Z) : Set :=
  {t : sch_tree | forall p:Z, In p l <-> sch_occ p t}.
 
Definition sch_list2tree_aux_spec (l:list Z) (t:sch_tree) :=
  {t' : sch_tree | forall p:Z, In p l \/ sch_occ p t <-> sch_occ p t'}.


Inductive sch_RMAX (t t':sch_tree) (n:Z) : Prop :=
    sch_rmax_intro :
      sch_occ n t ->
      (forall p:Z, sch_occ p t -> p <= n) ->
      (forall q:Z, sch_occ q t' -> sch_occ q t) ->
      (forall q:Z, sch_occ q t -> sch_occ q t' \/ n = q) ->
      ~ sch_occ n t' -> sch_RMAX t t' n
 .


Inductive sch_RM (n:Z) (t t':sch_tree) : Prop :=
    sch_rm_intro :
      ~ sch_occ n t' ->
      (forall p:Z, sch_occ p t' -> sch_occ p t) ->
      (forall p:Z, sch_occ p t -> sch_occ p t' \/ n = p) ->
       sch_RM n t t' .



Definition sch_rm_spec (n:Z) (t:sch_tree) : Set :=
     {t' : sch_tree | sch_RM n t t'}.


(* from the original development *)

Inductive RM (n:Z) (t t':Z_btree) : Prop :=
    rm_intro :
      ~ occ n t' ->
      (forall p:Z, occ p t' -> occ p t) ->
      (forall p:Z, occ p t -> occ p t' \/ n = p) ->
      search_tree t' -> RM n t t' .


Definition rm_spec (n:Z) (t:Z_btree) : Set :=
  search_tree t -> {t' : Z_btree | RM n t t'}.

Definition  RM_lemma : forall (n:Z) (t :Z_btree) (H: search_tree t),
                    (rm_spec n t) -> (sch_rm_spec n (exist _ t H)).
Proof.
  intros n t H H0; case H0.
  -  trivial.  
  -  intros x Hx; case Hx; intros H1 H2 H3 H4.
     exists (exist _ x H4); split ;unfold sch_occ; cbn ; auto.
Defined.

Definition  RM_lemma_R : forall (n:Z) (t :sch_tree), 
                (sch_rm_spec n t) ->  match t with 
                                       exist _ t0 H0 => rm_spec n t0 
                                      end. 
Proof. 
 destruct t; cbn. 
 -   inversion 1.
   generalize H0; case x0;  intros x1 H1 H2.
   exists x1;  inversion H2; split ; cbn in * |- * ; auto.
Defined.
 
