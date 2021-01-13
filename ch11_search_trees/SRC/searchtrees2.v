(* binary search trees on Z *)
(* (C) Pierre Castéran *)

Set Implicit Arguments.

Require Export ZArith.
Open Scope Z_scope.

(* binary trees *)

Inductive Z_btree : Set :=
| Z_leaf : Z_btree
| Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.


Definition  is_bnode (t: Z_btree) :  Prop :=
  match t with
  | Z_leaf => False
  | _ => True
  end.

(* n : Z occurs in some tree *)
Inductive occ (n:Z) : Z_btree -> Prop :=
| occ_root : forall t1 t2:Z_btree, occ n (Z_bnode n t1 t2)
| occ_l : forall (p:Z) (t1 t2:Z_btree), occ n t1 -> occ n (Z_bnode p t1 t2)
| occ_r : forall (p:Z) (t1 t2:Z_btree), occ n t2 -> occ n (Z_bnode p t1 t2)
.

#[export] Hint Constructors occ :  searchtrees.

Derive Inversion_clear OCC_INV with
    (forall (z z':Z) (t1 t2:Z_btree), occ z' (Z_bnode z t1 t2)).

Lemma occ_inv :
  forall (z z':Z) (t1 t2:Z_btree),
    occ z' (Z_bnode z t1 t2) -> z = z' \/ occ z' t1 \/ occ z' t2.
Proof.
  intros z z' t1 t2 H; inversion H using OCC_INV; auto with searchtrees.
Qed.

#[export] Hint Resolve occ_inv: searchtrees.

Lemma not_occ_Leaf : forall z:Z, ~ occ z Z_leaf.
Proof.
  unfold not; intros z H; inversion_clear H.
Qed.

#[export] Hint Resolve not_occ_Leaf: searchtrees.

(* z is less than every label in t *)

Inductive min (z:Z)  : Z_btree -> Prop :=
| min_leaf : min z Z_leaf
| min_bnode : forall (r:Z)(t1 t2:Z_btree),
    min z t1 -> min z t2 -> z < r ->
    min z (Z_bnode r t1 t2).

#[ export ] Hint Constructors min : searchtrees.

(* z is greater than every label in t *)
Inductive maj (z:Z)  : Z_btree -> Prop :=
| maj_leaf : maj z Z_leaf
| maj_bnode : forall (r:Z)(t1 t2:Z_btree),
    maj z t1 -> maj z t2 -> r < z ->
    maj z (Z_bnode r t1 t2).

#[export] Hint Constructors maj : searchtrees.

Lemma min_intro : forall (z : Z) (t : Z_btree), 
    (forall z':Z, occ z' t -> z < z') -> min z t.
Proof.
  induction t as [ | r t1 IHt1 t2 IHt2].
  - auto with searchtrees.
  - intro H; apply min_bnode.
    + apply IHt1;intros; apply H; eauto with searchtrees.
    +  apply IHt2;intros; apply H; eauto with searchtrees.
    + eauto with searchtrees.
Qed.

Lemma min_inv_root : forall (z r:Z)(t1 t2:Z_btree),
    min z (Z_bnode r t1 t2) -> z < r.
Proof.
  inversion_clear 1; auto.
Qed.

Lemma min_inv_l : forall (z r:Z)(t1 t2:Z_btree),
    min z (Z_bnode r t1 t2) -> min z t1.
Proof.
  inversion_clear 1; auto.
Qed.

Lemma min_inv_r : forall (z r:Z)(t1 t2:Z_btree),
    min z (Z_bnode r t1 t2) -> min z t2.
Proof.
  inversion_clear 1; auto.
Qed.

#[export] Hint Resolve min_inv_l min_inv_r min_inv_root : searchtrees.

Lemma min_less1 : forall (z : Z) (t : Z_btree),
    min z t -> (forall z', occ z' t ->  z < z').
Proof.
  induction 1.
  -  inversion 1.
  -  inversion 1;eauto with searchtrees.
Qed.

Lemma min_less : forall (z z': Z) (t : Z_btree),
    occ z' t -> min z t ->  z < z'.
Proof.
  intros; eapply min_less1; eauto.
Qed.


Lemma min_ind2 : forall (z : Z) (t : Z_btree) (P:Prop),
    ((forall z', occ z' t ->  z < z') -> P) ->
    min z t -> P.
Proof.
  induction t as [ | r t1 IHt1 t2 IHt2].
  -  intros P H H0; apply H.  
     inversion 1. 
  -  intros P H H0; apply H.  
     inversion_clear 1.
     + eauto with searchtrees.
     + apply min_less with (Z_bnode r t1 t2); eauto with searchtrees.
     + apply min_less with (Z_bnode r t1 t2); eauto with searchtrees.
Qed.

Lemma min_not_occ : forall (z:Z) (t:Z_btree), min z t -> ~ occ z t.
Proof.
  intros z t H H'; elim H using min_ind2.
  -  intro; absurd (z < z); auto.
     apply Z.lt_irrefl.
Qed.

