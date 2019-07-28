Require Import List Relations.

Set Implicit Arguments.

Section perms.
Variable A : Type.

 Inductive transpose : list A -> list A -> Prop :=
   | transpose_hd :
       forall (a b:A) (l:list A), transpose (a :: b :: l) (b :: a :: l)
   | transpose_tl :
       forall (a:A) (l l':list A),
         transpose l l' -> transpose (a :: l) (a :: l').


Inductive perm (l:list A) : list A -> Prop :=
  | perm_id : perm l l
  | perm_tr :
      forall l' l'':list A, perm l l' -> transpose l' l'' -> perm l l''.

Lemma perm_refl : reflexive _ perm. 
Proof.
  left.
Qed.

Lemma perm_intro_r :
 forall l1 l2 :list A, perm l1 l2 -> 
    forall l, transpose l l1 ->  perm l l2.
Proof.
 induction 1. 
 - intros l H; constructor 2 with l; [left | assumption]. 
 - intros l Hl; constructor 2 with  l';auto.
Qed.

Lemma perm_trans : transitive _ perm.
Proof.
 intros l l' l'' H; generalize l''.
 induction H as [|l0 l'0 H0 IHperm].
 -  trivial.
 -  intros l''0 H2;
    apply IHperm; eapply perm_intro_r; eauto.
Qed.

Lemma transpose_sym : forall l l':list A, transpose l l' -> transpose l' l.
Proof.
 intros l l' H;elim H; [ left | right; auto ].
Qed.

Lemma perm_sym : symmetric _ perm. 
Proof.
 unfold symmetric; intros l l' H; induction H as [|].
-  left.
 -  apply perm_intro_r with l'; [trivial | now apply transpose_sym].
Qed.


Theorem equiv_perm : equiv _ perm.
Proof.
 repeat split.
 -  apply perm_refl.
 -  apply perm_trans.
 -  apply perm_sym.
Qed.


End perms.
