Require Export Ltree  building  graft.

Set Implicit Arguments.

(*  having some infinite branch *)

CoInductive SomeInf (A:Type):(LTree A)->Prop :=
  InfLeft : forall (a:A)(t1 t2:LTree A),
    SomeInf t1 ->
    SomeInf (LBin a t1 t2)
|  InfRight : forall (a:A)(t1 t2:LTree A),
    SomeInf t2 ->
    SomeInf (LBin a t1 t2).

(*  every branch is infinite *)
CoInductive EveryInf (A:Type) :(LTree A)->Prop :=
  InfI : forall (a:A) (t1 t2: LTree A),
    EveryInf t1 ->
    EveryInf t2 ->
    EveryInf (LBin a t1 t2).


(* having some finite branch *)

Inductive SomeFin (A:Type) : (LTree A)->Prop :=
  SomeFin_leaf : SomeFin LLeaf
| SomeFin_left : forall (a:A) (t1 t2: LTree A),
    SomeFin t1 ->
    SomeFin (LBin a t1 t2)
| SomeFin_right : forall (a:A) (t1 t2: LTree A),
    SomeFin t2 ->
    SomeFin (LBin a t1 t2).

(* Every branch is finite (i.e. this is a finite tree) *)


Inductive Finite (A:Type) :(LTree A)->Prop :=
  Finite_leaf : Finite LLeaf 
| Finite_bin : forall (a:A) (t1 t2: LTree A),
    Finite t1 ->
    Finite t2 ->
    Finite (LBin a t1 t2).

#[export] Hint Resolve Finite_leaf Finite_bin SomeFin_leaf 
     SomeFin_left  SomeFin_right : core.



(* we prove that the tree built in module building has 
   only infinite branches *)

(* technical unfolding lemma *)

Lemma Positive_tree_from_unfold : 
  forall p, Positive_Tree_from p =
            LBin p (Positive_Tree_from (xO p)) (Positive_Tree_from (xI p)).
Proof.
  intros p; now LTree_unfold (Positive_Tree_from p).
Qed.  


Lemma Positive_tree_from_inf : forall p, EveryInf  (Positive_Tree_from  p).
Proof.
  cofix Positive_tree_from_inf.
  intro p; rewrite (Positive_tree_from_unfold p); split; auto.
Qed.

(* a tree with an infinite branch *)

CoFixpoint zigzag (b:bool): LTree bool :=
  if b then (LBin b LLeaf (zigzag false))
  else (LBin b (zigzag true) LLeaf ).

(*
       true
      /   \
    Leaf  false
          /   \
       true    Leaf
      /   \
    Leaf  false
          /   \
       true    Leaf
      /   \
    Leaf  false
          /   \
       true    Leaf
       ...
 *)



Lemma zigzag_unfold : forall b,
    zigzag b =
    if b
    then LBin b LLeaf (zigzag false)
    else LBin b (zigzag true) LLeaf.
Proof.
  intro b;LTree_unfold (zigzag b); cbn ; case b; simpl; auto.
Qed.

Lemma zigzag_inf : forall b, SomeInf (zigzag b).
Proof.
  cofix H;  intro b;   rewrite (zigzag_unfold b);
    case b; cbn; [right|left]; auto.
Qed.


(* Some Finite/Infinite relationships *)


Lemma Finite_Not_SomeInf : forall (A:Type) (t: LTree A),
    Finite t -> ~ SomeInf t.
Proof.
  intros A t H; induction  H as [| a t1 t2 H1 IHt1 H2 IHt2].
  -  red; inversion 1.
  -  inversion 1; tauto. 
Qed.


Lemma SomeInf_Not_Finite : forall (A:Type) (t: LTree A),
    SomeInf t -> ~ Finite t.
Proof.
  intros A t; generalize (Finite_Not_SomeInf (t:=t)); tauto.
Qed.


Lemma SomeFin_Not_EveryInf : forall (A:Type)(t: LTree A),
    SomeFin t -> ~ EveryInf t.
Proof.
  intros A t Ht; induction Ht;   red; inversion 1; auto.
Qed.

Lemma Not_SomeFin_EveryInf : forall (A:Type)(t: LTree A),
    ~ SomeFin t -> EveryInf t.
Proof.
  intros A ; cofix H.
  intro t; destruct  t as [| a t1 t2].
  -  destruct 1; constructor.
  -  intro H0; split ; apply H; red; auto. 
Qed.


Section classic.
  Hypothesis class:forall P:Prop, ~~P ->P.


  Remark demorgan : forall P Q, ~(~P /\ ~Q)-> P \/ Q.
  Proof.  
    intros; apply class; tauto.
  Qed.

  Remark  Not_Finite_or : forall (A:Type) (a:A) (t1 t2: LTree A),
      ~ Finite (LBin a t1 t2) ->
      ~ Finite t1  \/  ~Finite t2.
  Proof.
    intros A a t1 t2 H; apply demorgan;   intro; apply H.
    right; apply class; tauto.
  Qed.

  Lemma Not_Finite_SomeInf : forall (A:Type)(t: LTree A),
      ~Finite t -> SomeInf t.
  Proof.
    intro A; cofix the_thm.
    intro t ; destruct  t as [| a t1 t2].
    - destruct 1; left.
    - intro H; case (Not_Finite_or H); [left|right];
        apply the_thm ; auto.
  Qed.
  
End classic.

Theorem graft_Finite_LLeaf : forall (A:Type) (t: LTree A),
    Finite t ->
    graft t LLeaf = t.
Proof.
  intros A t H; induction H as  [| a t1 t2 H1 IHt1 H2 IHt2].
  -  rewrite graft_unfold; auto.
  -  rewrite graft_unfold, IHt1,  IHt2; auto.
Qed.

