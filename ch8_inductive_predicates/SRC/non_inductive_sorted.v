Require Export List Relations.

Section Definitions.
  Variables (A: Type)(R: relation A).
  Inductive sorted  : list A -> Prop :=
  | sorted0 : sorted  nil
  | sorted1 : forall x:A, sorted (x::nil)
  | sorted2 :
      forall (x y:A)(l:list A),
        R x y ->
        sorted  (y::l)-> sorted  (x :: y :: l).


  Definition sorted' (l:list A) :=
    forall (l1 l2:list A)(n1 n2:A),
      l = l1 ++ (n1 :: n2 ::l2) -> 
      R n1 n2.

  #[local] Hint Constructors sorted : core.


  (** Let us prove that sorted' satisfies the constructors of sorted 
   *)


  Lemma sorted'0 : sorted'   nil.
  Proof.
    intro l1;   case l1; simpl; intros; discriminate.
  Qed.

  Lemma sorted'1 : forall x, sorted'  (x::nil).
  Proof.
    intros  x l1 l2 n1 n2; case l1.
    -  simpl; discriminate.
    - intros a l1'; case l1'; simpl; discriminate.
  Qed.

  Lemma sorted'2 :
    forall x y l,
      R x y ->
      sorted' (y :: l)-> sorted' (x :: y :: l).
  Proof.
    intros x y l Hr Hs l1; case l1.
    -  intros l2 n1 n2 Heq; injection Heq; intros; subst; trivial.
    -  simpl; intros a l1' l2 n1 n2 Heq; injection Heq.
       intros Heq' Heqx; apply (Hs l1' l2); trivial.
  Qed.

  #[local] Hint Resolve sorted'0 sorted'1 sorted'2 : core.

  Lemma sorted'_inv : forall a l, sorted' (a::l) -> sorted' l.
  Proof.
    intros a l H l1 l2 n1 n2 e.
    apply (H (a::l1) l2 n1 n2); now rewrite e. 
  Qed.

  Lemma sorted_imp_sorted' :
    forall l, sorted l -> sorted'  l.
  Proof.
    intros l H; induction  H; auto.
  Qed.

  Lemma sorted'_imp_sorted: forall l, sorted' l -> sorted  l.
  Proof.
    induction l as [|a l']; auto.
    - destruct l'; auto.
      + intro H; constructor. 
        * apply (H nil l'); auto.
        *  apply IHl'; apply (sorted'_inv _ _ H).
  Qed.

End Definitions.
