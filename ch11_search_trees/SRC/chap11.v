(* binary search trees on Z *)
(* (C) Pierre Castéran *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Export ZArith.
Require Import Extraction.

Open Scope Z_scope.

(* binary trees *)

Inductive Z_btree : Set :=
| Z_leaf : Z_btree
| Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.


Definition is_bnode (t: Z_btree) : Prop :=
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

#[ export ] Hint  Constructors   occ  : searchtrees.

Derive Inversion_clear OCC_INV with
    (forall (z z':Z) (t1 t2:Z_btree), occ z' (Z_bnode z t1 t2)).

Lemma occ_inv :
  forall (z z':Z) (t1 t2:Z_btree),
    occ z' (Z_bnode z t1 t2) -> z = z' \/ occ z' t1 \/ occ z' t2.
Proof.
  inversion 1 using OCC_INV; auto with searchtrees.
Qed.

#[ export ] Hint Resolve occ_inv: searchtrees.

Lemma not_occ_Leaf : forall z:Z, ~ occ z Z_leaf.
Proof.
  unfold not;  inversion_clear 1.
Qed.

#[ export ] Hint Resolve not_occ_Leaf: searchtrees.

(* naive search *)

Definition naive_occ_dec : forall (n:Z) (t:Z_btree), {occ n t} + {~ occ n t}.
  intros n t; induction t as [| z t1 IH1 t2 IH2].
  -  right; auto with searchtrees.
  -  case (Z.eq_dec n z).
     + intro e; subst n;  left; auto with searchtrees.
     +  case IH1; case IH2; intros; auto with searchtrees.
        right; intro H; elim (occ_inv H); auto with searchtrees.
        tauto.
Defined.

(** Tests :
Extraction naive_occ_dec.
 *)
(* auxiliary definition for search, insertion and deletion *)

(* z is less than every label in t *)
Inductive min (z:Z) (t:Z_btree) : Prop :=
| min_intro : (forall z':Z, occ z' t -> z < z') -> min z t.

#[ export ] Hint Constructors min: searchtrees.

(* z is greater than every label in t *)
Inductive maj (z:Z) (t:Z_btree) : Prop :=
  maj_intro : (forall z':Z, occ z' t -> z' < z) -> maj z t
.

#[ export ] Hint Constructors maj: searchtrees.

(* search-ness predicate on binary trees *)
Inductive search_tree : Z_btree -> Prop :=
| leaf_search_tree : search_tree Z_leaf
| bnode_search_tree :
    forall (z:Z) (t1 t2:Z_btree),
      search_tree t1 ->
      search_tree t2 ->
      maj z t1 -> min z t2 -> search_tree (Z_bnode z t1 t2)
.

#[ export ] Hint Constructors search_tree : searchtrees.

Lemma min_leaf : forall z:Z, min z Z_leaf.
Proof.
  intro z; apply min_intro; intros z' H; inversion_clear H.
Qed.

#[ export ] Hint Resolve min_leaf: searchtrees.

Lemma maj_leaf : forall z:Z, maj z Z_leaf.
Proof.
  intro z; apply maj_intro; intros z' H; inversion_clear H.
Qed.

#[ export ] Hint Resolve maj_leaf: searchtrees.

Lemma maj_not_occ : forall (z:Z) (t:Z_btree), maj z t -> ~ occ z t.
Proof.
  intros z t H H'; elim H; intros; absurd (z < z); auto.
  apply Z.lt_irrefl.
Qed.

#[ export ] Hint Resolve maj_not_occ: searchtrees.

Lemma min_not_occ : forall (z:Z) (t:Z_btree), min z t -> ~ occ z t.
Proof.
  intros z t H H'; elim H; intros; absurd (z < z); auto.
  apply Z.lt_irrefl.
Qed.

#[ export ] Hint Resolve min_not_occ: searchtrees.

Section search_tree_basic_properties.

  Variable n : Z.
  Variables t1 t2 : Z_btree.
  Hypothesis se : search_tree (Z_bnode n t1 t2).

  Lemma search_tree_l : search_tree t1.
  Proof.
    inversion_clear se; auto with searchtrees.
  Qed.
  #[ local ] Hint Resolve search_tree_l: searchtrees.

  Lemma search_tree_r : search_tree t2.
  Proof.
    inversion_clear se; auto with searchtrees.
  Qed.
  #[local] Hint Resolve search_tree_r: searchtrees.

  Lemma maj_l : maj n t1.
  Proof.
    inversion_clear se; auto with searchtrees.
  Qed.
  #[local] Hint Resolve maj_l: searchtrees.

  Lemma min_r : min n t2.
  Proof.
    inversion_clear se; auto with searchtrees.
  Qed.
  #[local] Hint Resolve min_r: searchtrees.

  Lemma not_right : forall p:Z, p <= n -> ~ occ p t2.
  Proof.
    intros p H; elim min_r.
    unfold not; intros; absurd (n < p); auto with searchtrees.
    apply Zle_not_lt; assumption.
  Qed.

  #[local] Hint Resolve not_right: searchtrees.
  
  Lemma not_left : forall p:Z, p >= n -> ~ occ p t1.
  Proof.
    intros p H; elim maj_l.
    unfold not; intros; absurd (p < n); auto with searchtrees.
  Qed.

  #[local] Hint Resolve not_left: searchtrees.

  Lemma go_left : forall p:Z, occ p (Z_bnode n t1 t2) -> p < n -> occ p t1.
  Proof.
    intros p H H0;  elim (occ_inv H).
    -   intro e; elim e; absurd (p < n). 
        +   rewrite e; apply Zle_not_lt; auto with zarith. 
        +  assumption.
    -  destruct 1;auto.
       absurd (occ p t2).
       +   apply not_right;  apply Zlt_le_weak; assumption. 
       +   auto.
  Qed.

  Lemma go_right : forall p:Z, occ p (Z_bnode n t1 t2) -> p > n -> occ p t2.
  Proof.
    intros p H H0;   elim (occ_inv H).
    - intro e; elim e;   absurd (n < p). 
      +   rewrite e; apply Zle_not_lt; auto with zarith. 
      +   apply Z.gt_lt; assumption.
    -   destruct 1; auto.
        absurd (occ p t1).
        +    apply not_left; unfold Z.ge; rewrite H0; discriminate. 
        +   auto.
  Qed.

End search_tree_basic_properties.

#[ export ] Hint Resolve go_left go_right not_left not_right search_tree_l search_tree_r
 maj_l min_r: searchtrees.

(* A better search program *)

Definition occ_dec_spec (p:Z) (t:Z_btree) :=
  search_tree t -> {occ p t} + {~ occ p t}.



Definition occ_dec : forall (p:Z) (t:Z_btree), occ_dec_spec p t.
  refine
    (fix occ_dec (p:Z) (t:Z_btree) {struct t} : occ_dec_spec p t :=
       match t as x return occ_dec_spec p x with
       | Z_leaf => fun h => right _ _
       | Z_bnode n t1 t2 =>
         fun h =>
           match Z_le_gt_dec p n with
           | left h1 =>
             match Z_le_lt_eq_dec p n h1 with
             | left h'1 =>
               match occ_dec p t1 _ with
               | left h''1 => left _ _
               | right h''2 => right _ _
               end
             | right h'2 => left _ _
             end
           | right h2 =>
             match occ_dec p t2 _ with
             | left h''1 => left _ _
             | right h''2 => right _ _
             end
           end
       end); eauto with searchtrees.
  rewrite h'2; auto with searchtrees.
Defined.

Extraction occ_dec.
(*
let rec occ_dec p = function
  | Z_leaf -> Right
  | Z_bnode (n, t1, t2) ->
      (match z_le_gt_dec p n with
         | Left ->
             (match z_le_lt_eq_dec p n with
                | Left -> occ_dec p t1
                | Right -> Left)
         | Right -> occ_dec p t2)
 *)


(* 
 Definition of an INSERT predicate (a la  Prolog)
***************************************************

We begin with the definition of a predicate:

(INSERT n t t') if t' is a binary search tree containing exactly
  n and the elements of t *)

Inductive INSERT (n:Z) (t t':Z_btree) : Prop :=
  insert_intro :
    (forall p:Z, occ p t -> occ p t') ->
    occ n t' ->
    (forall p:Z, occ p t' -> occ p t \/ n = p) ->
    search_tree t' -> INSERT n t t'
.

#[ export ] Hint Resolve insert_intro: searchtrees.


Definition insert_spec (n:Z) (t:Z_btree) : Set :=
  search_tree t -> {t' : Z_btree | INSERT n t t'}.

Lemma insert_leaf : forall n:Z, INSERT n Z_leaf (Z_bnode n Z_leaf Z_leaf).
Proof.
  intro n; split; auto with searchtrees.
  intros p H; inversion_clear H; auto with searchtrees. 
Qed.

#[ export ] Hint Resolve insert_leaf: searchtrees.

(* Inserting in the left son *)

Lemma insert_l :
  forall (n p:Z) (t1 t'1 t2:Z_btree),
    n < p ->
    search_tree (Z_bnode p t1 t2) ->
    INSERT n t1 t'1 -> INSERT n (Z_bnode p t1 t2) (Z_bnode p t'1 t2).
Proof.
  intros n p t1 t'1 t2 H H0 H1; split.
  -  intros p0 H2; inversion_clear H2; auto with searchtrees.
     elim H1; auto with searchtrees.
  - constructor 2; elim H1; auto with searchtrees.
  -  intros p0 H2; inversion_clear H2; auto with searchtrees.
     elim H1.  intros H4 H5 H6.
     elim (H6 p0); auto with searchtrees.
  -  elim H1; constructor 2; auto with searchtrees.
     +  eapply search_tree_r; eauto with searchtrees.
     +  split; intros;     elim (H4 z').
        intro; cut (maj p t1).
        * induction 1; auto with searchtrees.
        * eapply maj_l; eauto with searchtrees.
        * intro e; subst z'; auto with searchtrees.
        * assumption.       
     + eapply min_r; eauto with searchtrees.
Qed.


Lemma insert_r :
  forall (n p:Z) (t1 t2 t'2: Z_btree),
    n > p ->
    search_tree (Z_bnode p t1 t2) ->
    INSERT n t2 t'2 -> INSERT n (Z_bnode p t1 t2) (Z_bnode p t1 t'2).
(*******************************************************)
Proof.
  intros n p t1 t2 t'2 H H0 H1; split.
  - intros p0 H2; inversion_clear H2; auto with searchtrees.
    elim H1; auto with searchtrees.
  -  constructor 3; elim H1; auto with searchtrees.
  -  intros p0 H2; inversion_clear H2; auto with searchtrees.
     elim H1; intros H4 H5 H6.
     elim (H6 p0); auto with searchtrees.
  -  elim H1; constructor 2; auto with searchtrees.
     + eapply search_tree_l; eauto with searchtrees.
     + split; intros; elim (maj_l H0); auto with searchtrees.
     +  split; intros q H6; elim (H4 q H6).
        intro; elim (min_r H0); auto with searchtrees.
        intro e; subst q;  auto with searchtrees.
        apply Z.gt_lt.
        assumption.
Qed.

Lemma insert_eq :
  forall (n:Z) (t1 t2:Z_btree),
    search_tree (Z_bnode n t1 t2) ->
    INSERT n (Z_bnode n t1 t2) (Z_bnode n t1 t2).
Proof.
  auto with searchtrees.
Qed.

#[ export ] Hint Resolve insert_l insert_r insert_eq: searchtrees.



Definition insert : forall (n:Z) (t:Z_btree), insert_spec n t.
  refine
    (fix insert (n:Z) (t:Z_btree) {struct t} : insert_spec n t :=
       match t return insert_spec n t with
       | Z_leaf => fun s => exist _ (Z_bnode n Z_leaf Z_leaf) _
       | Z_bnode p t1 t2 =>
         fun s =>
           match Z_le_gt_dec n p with
           | left h =>
             match Z_le_lt_eq_dec n p h with
             | left _ =>
               match insert n t1 _ with
               | exist _ t3 _ => exist _ (Z_bnode p t3 t2) _
               end
             | right _ => exist _ (Z_bnode n t1 t2) _
             end
           | right _ =>
             match insert n t2 _ with
             | exist _ t3 _ => exist _ (Z_bnode p t1 t3) _
             end
           end
       end); eauto with searchtrees.
  rewrite e; eauto with searchtrees.
Defined.


(** Tests :
Extraction insert.
 *)

(*
let rec insert n = function
  | Z_leaf -> Z_bnode (n, Z_leaf, Z_leaf)
  | Z_bnode (p, t1, t2) ->
      (match z_le_gt_dec n p with
         | Left ->
             (match z_le_lt_eq_dec n p with
                | Left -> Z_bnode (p, (insert n t1), t2)
                | Right -> Z_bnode (n, t1, t2))
         | Right -> Z_bnode (p, t1, (insert n t2)))
 *)



Require Export List.

#[ export ] Hint Resolve in_nil: searchtrees.

#[ export ] Hint Resolve in_inv: searchtrees.




(* Construction of a binary search tree containing the elements of
  a list of integers *)


Definition list2tree_spec (l:list Z) : Set :=
  {t : Z_btree | search_tree t /\ (forall p:Z, In p l <-> occ p t)}.


Definition list2tree_aux_spec (l:list Z) (t:Z_btree) :=
  search_tree t ->
  {t' : Z_btree |
    search_tree t' /\ (forall p:Z, In p l \/ occ p t <-> occ p t')}.


Definition list2tree_aux :
  forall (l:list Z) (t:Z_btree), list2tree_aux_spec l t.
  refine
    (fix list2tree_aux (l:list Z) : forall t:Z_btree, list2tree_aux_spec l t :=
       fun t =>
         match l return list2tree_aux_spec l t with
         | nil => fun s => exist _ t _
         | cons p l' =>
           fun s =>
             match insert p (t:=t) s with
             | exist _ t' _ =>
               match list2tree_aux l' t' _ with
               | exist _ t'' _ => exist _ t'' _
               end
             end
         end).
  -  split; auto.
     +  split; auto.
        *     induction 1; auto.
              inversion H.
  -  case i; auto.
  - case a; auto.
    intros; split; auto.
    intros; case a; intros; split; auto.
    destruct  1 as [H3 | H3].
    +  case H3.
       *   intro e; rewrite <- e.
           case (H2 p); intros; apply H4; right; case i; auto.
       *  case (H2 p0); auto. 
    +  case (H2 p0); auto.
       intros H4 H5; apply H4; right.
       elim i; auto.
    + intros; case a; auto;  intros H4 H5.
      case (H5 p0); intros H6 H7; case (H7 H3).
      left; auto.
      cbn; auto.
      case i.
      intros H8 H9 H10 H11 H12.
      case (H10 p0 H12); auto.
      induction 1; cbn; auto.
Defined.

Definition list2tree : forall l:list Z, list2tree_spec l.
  refine
    (fun l =>
       match list2tree_aux l (t:=Z_leaf) _ with
       | exist _ t _ => exist _ t _
       end).
  Proof.
    eauto with searchtrees.
    case a; auto.
    split; auto.
    intro p; split; case (H0 p).
    - auto.
    -  intros H1 H2 H3; case (H2 H3); auto.
       inversion 1.
  Defined.

  (*
Extraction list2tree_aux. 

let rec list2tree_aux l t =
  match l with
    | Nil -> t
    | Cons (p, l') -> list2tree_aux l' (insert p t)

Extraction list2tree.

let list2tree l =
  list2tree_aux l Z_leaf
   *)


  (** removing the greates element in a search-tree 

   *)
  Inductive RMAX (t t':Z_btree) (n:Z) : Prop :=
    rmax_intro :
      occ n t ->
      (forall p:Z, occ p t -> p <= n) ->
      (forall q:Z, occ q t' -> occ q t) ->
      (forall q:Z, occ q t -> occ q t' \/ n = q) ->
      ~ occ n t' -> search_tree t' -> RMAX t t' n
  .

  #[ export ] Hint Constructors RMAX : searchtrees.


  (* base cases *)

  Lemma rmax_leaf_leaf : forall n:Z, RMAX (Z_bnode n Z_leaf Z_leaf) Z_leaf n.
  Proof.
    intro n; split; auto with searchtrees.
    -  intros p H; inversion_clear H; auto with searchtrees.
       +  auto with zarith.   
       +  absurd (occ p Z_leaf); auto with searchtrees.
       +  absurd (occ p Z_leaf); auto with searchtrees.
    -   inversion_clear 1 ; auto with searchtrees.
  Qed.


  Lemma rmax_t_Z_leaf :
    forall (t:Z_btree) (n:Z),
      search_tree (Z_bnode n t Z_leaf) -> RMAX (Z_bnode n t Z_leaf) t n.
  Proof.
    intros t n H; split; auto with searchtrees. 
    -  intros p H0; elim (occ_inv H0); intro H1.
       + subst p; auto with zarith.
       +  elim H1; intro H2.
          *  apply Zlt_le_weak;  elim (maj_l H); auto.
          *  absurd (occ p Z_leaf); auto with searchtrees.
    - intros q H1; elim (occ_inv H1); intros H0; auto with searchtrees.
      destruct  H0; auto.
      inversion H0.
    -  intro H'; absurd (occ n Z_leaf).
       +      auto with searchtrees.  
       +      destruct (not_left H (p:=n)).
              *      auto with zarith.
              *      auto with searchtrees.
    -  eauto with searchtrees. 
  Qed. 

  #[ export ] Hint Resolve rmax_t_Z_leaf: searchtrees.


  (* We study the case of a search tree (Z_bnode n t1 (Z_bnode p t2 t3))  *)

  Section RMAX_np.
    Variables n p q : Z.
    Variables t1 t2 t3 t' : Z_btree.
    Hypothesis S1 : search_tree (Z_bnode n t1 (Z_bnode p t2 t3)).
    Hypothesis R1 : RMAX (Z_bnode p t2 t3) t' q.
    #[ local] Hint Resolve S1 R1: searchtrees.
    
    Lemma rmax_1 : occ q (Z_bnode n t1 (Z_bnode p t2 t3)).
    Proof.
      elim R1; auto with searchtrees.
    Qed.

    #[local] Hint Resolve rmax_1: searchtrees.

    Lemma rmax_2 : n < p.
    Proof.
      elim (min_r S1); auto with searchtrees.
    Qed.

    #[local] Hint Resolve rmax_2: searchtrees.
    
    Lemma rmax_3 : min n t'. 
    Proof.
      apply min_intro.
      intros q' H; elim R1; intros.
      elim (min_r S1); auto with searchtrees.
    Qed.

    #[local] Hint Resolve rmax_3: searchtrees.
    
    Lemma rmax_4 : search_tree (Z_bnode n t1 t').
    Proof.
      right.
      -  apply search_tree_l with n (Z_bnode p t2 t3); auto with searchtrees. 
      -  elim R1; auto with searchtrees.
      -  apply maj_l with (Z_bnode p t2 t3); auto with searchtrees.
      -  auto with searchtrees.
    Qed. 

    #[local] Hint Resolve rmax_4: searchtrees.
    
    Lemma rmax_5 : n < q.
    Proof.
      elim R1; intros; apply Z.lt_le_trans with p; auto with searchtrees.
    Qed.

    #[local] Hint Resolve rmax_5: searchtrees.

    Lemma rmax_6 :
      forall p0:Z, occ p0 (Z_bnode n t1 (Z_bnode p t2 t3)) -> p0 <= q.

    Proof.
      intros p0 H; elim R1;  intros H0 H1 H2 H3 H4 H5.
      elim (occ_inv H); intro H6.
      - elim H6; apply Zlt_le_weak; auto with searchtrees  zarith.
      - elim H6; intro H7;  elim (maj_l S1). 
        intro H8; cut (p0 < n); auto with searchtrees.
        intro; apply Zlt_le_weak;  apply Z.lt_trans with n;
          auto with searchtrees.
        elim (min_r S1); auto with searchtrees.
    Qed.

    #[local] Hint Resolve rmax_6: searchtrees.
    
    Lemma rmax_7 :
      forall q':Z,
        occ q' (Z_bnode n t1 t') -> occ q' (Z_bnode n t1 (Z_bnode p t2 t3)).
    Proof.
      intros q' H; elim (occ_inv H); intro H0.
      -  elim H0; auto with searchtrees.
      -  elim H0; auto with searchtrees. 
         intro H1; elim R1; auto with searchtrees.
    Qed.

    #[local] Hint Resolve rmax_7: searchtrees.
    
    Lemma rmax_8 : ~ occ q (Z_bnode n t1 t').
    Proof.
      intro F;case  (occ_inv F).
      +  intro eg; absurd (n < q).
         *  rewrite eg;  apply Z.lt_irrefl.
         *  auto with searchtrees.
      +  intro H1; case H1; intro H2.
         * absurd (occ q t1); auto with searchtrees. 
           apply not_left with n (Z_bnode p t2 t3); auto with searchtrees.
           apply Z.le_ge; elim R1; auto with searchtrees.
         *  elim R1; auto.
    Qed.

    #[local] Hint Resolve rmax_8: searchtrees.

    Lemma rmax_9 :
      forall q0:Z,
        occ q0 (Z_bnode n t1 (Z_bnode p t2 t3)) ->
        occ q0 (Z_bnode n t1 t') \/ q = q0.
    Proof.
      intros q0 H; elim (occ_inv H).
      -   intro e; elim e;  left; auto with searchtrees.
      -   intro d; case d; intro H'.
          +  left; auto with searchtrees.
          +   elim R1; intros H1 H2 H3 H4 H5 H6.
              elim (H4 _ H'); auto with searchtrees.
    Qed.

    #[local] Hint Resolve rmax_9: searchtrees.

    Lemma rmax_t1_t2t3 :
      RMAX (Z_bnode n t1 (Z_bnode p t2 t3)) (Z_bnode n t1 t') q.
    Proof.
      apply rmax_intro; auto with searchtrees.
    Qed.

  End RMAX_np.

  #[ export ] Hint Resolve rmax_t1_t2t3: searchtrees.

  Definition rmax_sig (t:Z_btree) (q:Z) := {t' : Z_btree | RMAX t t' q}. 

  Definition rmax_spec (t:Z_btree) :=
    search_tree t -> is_bnode t -> {q : Z &  rmax_sig t q}.

  Definition rmax : forall t:Z_btree, rmax_spec t.
    refine
      (fix rmax (t:Z_btree) : rmax_spec t :=
         match t as x return rmax_spec x with
         | Z_leaf => fun h h' => False_rec _ _
         | Z_bnode r t1 t2 =>
           match
             t2 as z return rmax_spec z -> z = t2 -> rmax_spec (Z_bnode r t1 z)
           with
           | Z_leaf =>
             fun h h' h'' h''' =>
               existT (fun q:Z => rmax_sig (Z_bnode r t1 Z_leaf) q) r
                      (exist _ t1 _)
           | Z_bnode n' t'1 t'2 =>
             fun h h' h'' h''' =>
               match rmax t2 _ _ with
               | existT _ num (exist _ t' _) =>
                 existT
                   (fun q:Z =>
                      rmax_sig (Z_bnode r t1 (Z_bnode n' t'1 t'2)) q) num
                   (exist _ (Z_bnode r t1 t') _)
               end
           end _ _
         end).
    -  inversion h'.
    -  auto with searchtrees.
    -  case h'; eauto with searchtrees.
    -  case h'; eauto with searchtrees.
    -  rewrite h'; eauto with searchtrees.
       case h'; apply rmax_t1_t2t3; auto.
       rewrite h'; auto.
    -  auto.
    -  auto.
  Defined.



  (* VI    Deletion.
   ******************
   *******************


  Deleting an element from a binary search tree is a little more
  complex than inserting or searching.
  The difficult case is the deletion of the root of a tree; we have
  to reconstruct a search tree. To solve this problem, we define
  an auxiliary operation: deleting the greatest element of a non-empty
  binary search tree.
   *)

  (* VI.2  Deletion in general
   ****************************

  We are now ready to study the remove operation in it's generality:
 (RM n t t') if t' is a search tree obtained by removing n from t *)


  Inductive RM (n:Z) (t t':Z_btree) : Prop :=
    rm_intro :
      ~ occ n t' ->
      (forall p:Z, occ p t' -> occ p t) ->
      (forall p:Z, occ p t -> occ p t' \/ n = p) ->
      search_tree t' -> RM n t t' .


  Definition rm_spec (n:Z) (t:Z_btree) : Set :=
    search_tree t -> {t' : Z_btree | RM n t t'}.

  #[ export ] Hint Resolve rm_intro: searchtrees.


  (* base cases *)

  Lemma RM_0 : forall n:Z, RM n Z_leaf Z_leaf.
  Proof.
    intro n; apply rm_intro; auto with searchtrees.
  Qed.

  #[export] Hint Resolve RM_0: searchtrees.


  Lemma RM_1 : forall n:Z, RM n (Z_bnode n Z_leaf Z_leaf) Z_leaf.
  Proof.
    intros; apply rm_intro; auto with searchtrees.
    intros p H; elim (occ_inv H); auto with searchtrees.
    tauto.
  Qed.

  #[ export ] Hint Resolve RM_1: searchtrees.


  (* deleting in the left son *)

  Lemma rm_left :
    forall (n p:Z) (t1 t2 t':Z_btree),
      p < n ->
      search_tree (Z_bnode n t1 t2) ->
      RM p t1 t' -> RM p (Z_bnode n t1 t2) (Z_bnode n t' t2).
  Proof.
    intros n p t1 t2 t' H H0 H1.
    apply rm_intro. 
    - intro H2; elim (occ_inv H2).
      + intro eg; apply Z.lt_irrefl with n.
        pattern n at 1; rewrite eg; auto.  
      +  intro D; elim D; intro H3. 
         elim H1; auto with searchtrees.
         absurd (occ p t2); auto with searchtrees.
         apply not_right with n t1; auto with searchtrees.
         apply Zlt_le_weak; auto with searchtrees.
    -  intros p0 H2; elim (occ_inv H2).
       +  intro e; case e; auto with searchtrees.
       +  intro d; case d; auto with searchtrees.
          intro; elim H1; auto with searchtrees.
    -    intros p0 H2; elim (occ_inv H2).
         +  intro e; case e; auto with searchtrees.
         +  intro d; case d; intro H4.
            elim H1;  intros H5 H6 H7 H8.
            elim (H7 p0 H4); auto with searchtrees.
            auto with searchtrees.
    -  right. 
       +  elim H1; auto with searchtrees.
       +  apply search_tree_r with n t1; auto with searchtrees.
       +  apply maj_intro; intros q H2.
          cut (occ q t1).
          *  intro; elim (maj_l H0); intros; auto with searchtrees.
          *  auto with searchtrees.
             elim H1; auto with searchtrees.
       +  apply min_r with t1; auto with searchtrees.
  Qed.

  #[ export ] Hint Resolve rm_left: searchtrees.


  (* deleting in the right son *)

  Lemma rm_right :
    forall (n p:Z) (t1 t2 t':Z_btree),
      n < p ->
      search_tree (Z_bnode n t1 t2) ->
      RM p t2 t' -> RM p (Z_bnode n t1 t2) (Z_bnode n t1 t').
  Proof.
    intros n p t1 t2 t' H H0 H1; apply rm_intro.
    - intro H2; elim (occ_inv H2).
      +  intro eg; apply Z.lt_irrefl with p; auto with searchtrees.
         pattern p at 1; rewrite <- eg; auto with searchtrees.
      +  intro D; elim D; intro H3; elim H1; auto with searchtrees.
         absurd (occ p t1); auto with searchtrees.
         apply not_left with n t2; auto with searchtrees.
         apply Z.le_ge; apply Zlt_le_weak; auto.
    - intros p0 H2; elim (occ_inv H2).
      + intro e ; elim e; auto with searchtrees.
      + intro d ; elim d; auto with searchtrees.
        intro; elim H1; auto with searchtrees.
    -  intros p0 H2; elim (occ_inv H2).
       +  intro e ; elim e; auto with searchtrees.
       +  intro d ; elim d; intro H4.
          elim H1; intros H5 H6 H7 H8.
          left. auto with searchtrees. 
          elim H1; intros H5 H6 H7 H8.
          elim (H7 p0 H4); auto with searchtrees.
    -  right.
       eauto with searchtrees.
       elim H1; auto.
       + eauto with searchtrees.
       +   eapply min_r with t1; elim H1; intros H2 H3 H4 H5.
           inversion_clear H0.
           right; auto.
           *  elim H9;split; intros.
              apply H0.
              elim H1; auto with searchtrees.
  Qed.

  #[ export ] Hint Resolve rm_right: searchtrees.


  (* base case for deleting the root *)

  Lemma rm_root_base_case :
    forall (n:Z) (t:Z_btree),
      search_tree (Z_bnode n Z_leaf t) -> RM n (Z_bnode n Z_leaf t) t.
  Proof.
    intros; apply rm_intro.
    -  apply not_right with n Z_leaf; auto with searchtrees.
       reflexivity.  
    -  auto with searchtrees.  
    - intros p H1; elim (occ_inv H1); intro H2.
      +  right; auto.
      +  case H2; intro.
         *  absurd (occ p Z_leaf); auto with searchtrees.
         *  now left. 
    - apply search_tree_r with n Z_leaf; auto with searchtrees.
  Qed.

  #[ export ] Hint Resolve rm_root_base_case: searchtrees.


  (* General case: we use the RMAX predicate *)

  Section rm_root.
    Variables n p : Z.
    Variables t1 t2 t' : Z_btree.
    Hypothesis S : search_tree (Z_bnode n (Z_bnode p t1 t2) t').
    Variable q : Z.
    Variable t0 : Z_btree.
    Hypothesis R : RMAX (Z_bnode p t1 t2) t0 q.
    #[local] Hint Resolve S: searchtrees.
    
    Lemma rm_2 : q < n.
    (********************)
    Proof.
      elim R;  intros H H0 H1 H2 H3 H4.
      elim (maj_l (n:=n) (t1:=(Z_bnode p t1 t2)) (t2:=t'));  auto.
    Qed.

    #[local] Hint Resolve rm_2: searchtrees.
    
    Lemma rm_3 : ~ occ n (Z_bnode q t0 t').
    Proof.
      intro H; case  (occ_inv H).
      -  intro eg; absurd (q < q); auto with searchtrees.
         apply Z.lt_irrefl.
         pattern q at 2; rewrite eg; auto with searchtrees.
      - intro D; elim D; intro H'.
        +  elim R; intros H0 H1 H2 H3 H4 H5.
           absurd (occ n (Z_bnode p t1 t2)); auto with searchtrees.
           apply not_left with n t'; auto with searchtrees.
           apply Z.le_ge; auto with zarith.
        +   absurd (occ n t'); auto with searchtrees.
            apply not_right with n (Z_bnode p t1 t2); auto with searchtrees.
            auto with zarith. 
    Qed.

    #[local] Hint Resolve rm_3: searchtrees.

    Lemma rm_4 :
      forall p0:Z,
        occ p0 (Z_bnode q t0 t') -> occ p0 (Z_bnode n (Z_bnode p t1 t2) t').
    Proof. 
      intros p0 H; case (occ_inv H).  
      - intro eg; elim R; rewrite eg; auto with searchtrees.
      - intro D; elim D; auto with searchtrees.
        intro H'; elim R; auto with searchtrees.
    Qed.

    #[local] Hint Resolve rm_4: searchtrees.

    Lemma rm_5 :
      forall p0:Z,
        occ p0 (Z_bnode n (Z_bnode p t1 t2) t') ->
        occ p0 (Z_bnode q t0 t') \/ n = p0.
    Proof.
      intros p0 H; case  (occ_inv H). 
      -  intro e ; elim e; auto with searchtrees.
      -  intro H1;  case H1; intro H'1.
         +  elim R; intros H2 H3 H4 H5 H6 H7;
              elim (H5 p0 H'1); left; auto with searchtrees.
            subst p0; auto with searchtrees.
         +  left; auto with searchtrees.
    Qed.

    #[local] Hint Resolve rm_5: searchtrees.

    Lemma rm_6 : search_tree (Z_bnode q t0 t').
    Proof.
      right.
      - elim R; auto with searchtrees.
      -  apply search_tree_r with n (Z_bnode p t1 t2); auto with searchtrees.
      -  elim R; intros H H0 H1 H2 H3 H4; apply maj_intro; intros q0 H5.
         elim (Zle_lt_or_eq  _ _ (H0 q0 (H1 q0 H5))); auto.
         + intro eg; absurd (occ q0 t0);auto.
           rewrite eg; auto with searchtrees.
      - apply min_intro; intros q0 H;  apply Z.lt_trans with n. 
        + elim R; auto with searchtrees.
        +  elim (min_r (n:=n) (t1:=(Z_bnode p t1 t2)) (t2:=t'));
             auto with searchtrees. 
    Qed.

    #[local] Hint Resolve rm_6: searchtrees.
    

    Lemma rm_root_lemma :
      RM n (Z_bnode n (Z_bnode p t1 t2) t') (Z_bnode q t0 t').
    Proof.
      apply rm_intro; auto with searchtrees.  
    Qed.
    
  End rm_root.

  #[ export ] Hint Resolve rm_root_lemma: searchtrees.

  (* The final algorithm *)

  Definition rm : forall (n:Z) (t:Z_btree), rm_spec n t.
    (* We have to be careful to avoid introducing the hypothesis that
   the input tree is a search tree (hypothesis h) too early to prevent
   from too much  rewriting. *)
    refine
      (fix rm (n:Z) (t:Z_btree) {struct t} : rm_spec n t :=
         match t return rm_spec n t with
         | Z_leaf => fun h => exist _ Z_leaf _
         | Z_bnode z t1 t2 =>
           match Z_le_gt_dec n z with
           | left H0 =>
             (* H0:(le n z) *)
             match Z_le_lt_eq_dec _ _ H0 with
             | left H1 =>
               (* H1:(lt n z) *)
               fun h =>
                 match rm n t1 _ with
                 | exist _ t'1 H'1 => exist _ (Z_bnode z t'1 t2) _
                 end
             | right H1 =>
               (* H1:n=z *)
               match H1 in (_ = x) return rm_spec n (Z_bnode x t1 t2) with
               (* This cases construct corresponds to a Rewrite *)
               | refl_equal =>
                 match t1 as t return rm_spec n (Z_bnode n t t2) with
                 | Z_leaf => fun h => exist _ t2 _
                 | Z_bnode p' t'1 t'2 =>
                   fun h =>
                     match rmax (t:=(Z_bnode p' t'1 t'2)) _ _ with
                     | existT _ q (exist _ t'' H3) =>
                       exist _ (Z_bnode q t'' t2) _
                     end
                 end
               end
             end
           | right H0 =>
             fun h =>
               match rm n t2 _ with
               | exist _ t'2 H'2 => exist _ (Z_bnode z t1 t'2) _
               end
           end
         end); clear rm; eauto with searchtrees zarith.
    now cbn.
  Defined.

  (** Tests ;

Extraction rmax.
Extraction rm.
   *)

