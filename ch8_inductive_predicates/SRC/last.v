Require Import List.
Section Last.

  Variable A : Type.
  Set Implicit Arguments.

  Inductive last (a:A) : list A -> Prop :=
  | last_hd : last a (a :: nil)
  | last_tl : forall (b:A) (l:list A), last a l -> last a (b :: l).


  #[local] Hint Constructors last : core.

  Fixpoint last_fun (l:list A) : option A :=
    match l with
    | nil => None (A:=A)
    | a :: nil => Some a
    | a :: l' => last_fun l'
    end.

  Theorem last_fun_correct :
    forall (a:A) (l:list A), last a l -> last_fun l = Some a.
  Proof.
    intros a l H; induction H as [| b l H IH].  
    - reflexivity. 
    -   destruct l; simpl in *.
        +  discriminate IH.
        +  assumption. 
  Qed.

  Theorem last_fun_correct_R :
    forall (a:A) (l:list A), last_fun l = Some a -> last a l.
  Proof.
    intros a l ; induction l as [ |a0 l0 IHl0]; simpl.
    - discriminate.
    -  destruct l0.
       + injection 1;intros;subst a0;auto.
       +  intro e; simpl; auto. 
  Qed.

  Lemma last_fun_of_cons : forall (l:list A) (a:A), last_fun (a :: l) <> None.
  Proof.
    intros l ; induction l as [| a l0].
    -  discriminate.
    - destruct l0;simpl;auto.   
      + discriminate.
  Qed.

  Theorem last_fun_correct3 :
    forall l:list A, last_fun l = None -> forall b:A, ~ last b l.
  Proof.
    intro l; case l.
    - simpl; red; inversion 2.
    -  intros a l0 H;  case (last_fun_of_cons l0 a H). 
  Qed.

End Last.
