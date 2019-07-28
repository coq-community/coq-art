(* (c) P. Casteran *)

Set Implicit Arguments.
Require Export List.

(* potentialy infinite trees with internal nodes labeled with type A *)

CoInductive LTree (A:Type) : Type :=
  LLeaf : LTree A
| LBin : A -> LTree A -> LTree A -> LTree A.

Arguments LLeaf {A}.

(** Decomposition lemmas *)

Definition LTree_decomp {A:Type} (t: LTree A) : LTree A
  := match t with
         LLeaf => LLeaf
       | LBin a t1 t2 => (LBin  a t1 t2)
       end.

Lemma LTree_decompose {A: Type} : 
   forall t: LTree A, t = LTree_decomp t.
Proof.
 destruct t; reflexivity.
Qed.

Ltac  LTree_unfold term :=
  apply trans_equal with (1 := LTree_decompose term).



Definition is_LLeaf {A:Type} (t:LTree A) : Prop :=
  match t with
  | LLeaf => True
  | _ => False
  end.

Definition L_root {A:Type} (t:LTree A) : option A :=
  match t with
  | LLeaf => None
  | LBin r _ _ => Some r
  end.

Definition L_left_son {A:Type} (t:LTree A) : option (LTree A) :=
  match t with
  | LLeaf => None
  | LBin _ t1 _ => Some t1
  end.

Definition L_right_son {A:Type} (t:LTree A) : option (LTree A) :=
  match t with
  | LLeaf => None
  | LBin _ _ t2 => Some t2
  end.


Inductive direction : Type :=
  | d0 : direction (* left *)
  | d1 : direction (* right *).


Definition path := list direction.


(* The subtree at path p *)

Fixpoint L_subtree {A:Type} (p:path) (t:LTree A) {struct p} :
 option (LTree A) :=
  match p with
  | nil => Some t
  | d0 :: p' =>
      match t with
      | LLeaf => None
      | LBin a t1 t2 => L_subtree p' t1
      end
  | d1 :: p' =>
      match t with
      | LLeaf => None
      | LBin a t1 t2 => L_subtree p' t2
      end
  end.



(* the label at path p *)
    
Definition LTree_label {A:Type} (t:LTree A) (p:path) : 
  option A :=
  match L_subtree p t with
  | None => None
  | Some t' =>
      match t' with
      | LLeaf => None 
      | LBin x _ _ => Some x 
      end
  end.


Lemma LTree_label_rw_leaf {A: Type} :
 forall  (d:direction) (p:path), 
   LTree_label (LLeaf (A:=A)) (d :: p) = None.
Proof.
  unfold LTree_label in |- *; intros  d p; case d; simpl in |- *; auto.
Qed.


Lemma LTree_label_rw_root_bin {A: Type}:
 forall  (a:A) (t1 t2:LTree A),
   LTree_label (LBin a t1 t2) nil = Some a .
Proof.
  unfold LTree_label in |- *; simpl in |- *; auto.
Qed.

Lemma LTree_label_rw_root_leaf  {A: Type}:
   LTree_label (LLeaf (A:=A)) nil = None. 
Proof.
  unfold LTree_label in |- *; simpl in |- *; auto.
Qed.

Lemma LTree_label_rw0 {A: Type}:
 forall  (a:A) (t1 t2:LTree A) (p:path),
   LTree_label (LBin a t1 t2) (d0 :: p) = LTree_label t1 p.
Proof.
  unfold LTree_label in |- *; simpl in |- *; auto.
Qed.

Lemma LTree_label_rw1 {A:Type} :
 forall  (a:A) (t1 t2:LTree A) (p:path),
   LTree_label (LBin a t1 t2) (d1 :: p) = LTree_label t2 p.
Proof.
  unfold LTree_label in |- *; simpl in |- *; auto.
Qed.
