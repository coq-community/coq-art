(* Lazy lists . P. Castéran after Eduardo Gimenez *)
(**************************************************)
Require Export   Arith List RelationClasses.
Set Implicit Arguments.

CoInductive LList (A:Type) : Type :=
| LNil : LList A
| LCons : A -> LList A -> LList A.

Arguments LNil {A}.

(** Tests :
Check (LCons 1 (LCons 2 (LCons 3 LNil))).

 *)

Definition isEmpty (A:Type) (l:LList A) : Prop :=
  match l with
  | LNil => True
  | LCons a l' => False
  end.


Definition LHead (A:Type) (l:LList A) : option A :=
  match l with
  | LNil => None 
  | LCons a l' => Some a
  end.


Definition LTail (A:Type) (l:LList A) : LList A :=
  match l with
  | LNil => LNil 
  | LCons a l' => l'
  end.


Fixpoint LNth (A:Type) (n:nat) (l:LList A) {struct n} : 
  option A :=
  match l with
  | LNil => None 
  | LCons a l' => match n with
                  | O => Some a
                  | S p => LNth p l'
                  end
  end.


(** Tests :

Compute  (LNth 2 (LCons 4 (LCons 3 (LCons 90 LNil)))).

 *)


CoFixpoint from (n:nat) : LList nat := LCons n (from (S n)).

Definition Nats : LList nat := from 0.


(** Tests :

Eval cbn in (isEmpty Nats).

Eval cbv beta delta in (isEmpty Nats).

Eval cbn in (from 3).

Compute  (from 3).

Eval cbn in (LHead (LTail (from 3))).

Eval cbn in (LNth 19 (from 17)).

 *)

CoFixpoint omega_repeat (A:Type) (a:A) : LList A := LCons a (omega_repeat a).

CoFixpoint LAppend (A:Type) (u v:LList A) : LList A :=
  match u with
  | LNil => v
  | LCons a u' => LCons a (LAppend u' v)
  end.

(** Tests : 

Compute  LNth 123 (LAppend (omega_repeat 33) Nats).

Compute LNth 123 (LAppend (LCons 0 (LCons 1 (LCons 2 LNil))) Nats).

 *)

CoFixpoint general_omega (A:Type) (u v:LList A) : LList A :=
  match v with
  | LNil => u
  | LCons b v' =>
    match u with
    | LNil => LCons b (general_omega v' (LCons b v'))
    | LCons a u' => LCons a (general_omega u' (LCons b v'))
    end
  end.

Definition omega (A:Type) (u:LList A) : LList A := general_omega u u.

(** Tests : 
Compute LNth 3
        (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil))).


Compute  LNth 15 (LAppend (omega_repeat 33) (omega_repeat 69)).

 *)

Definition LList_decomp (A:Type) (l:LList A) : LList A :=
  match l with
  | LNil => LNil
  | LCons a l' => LCons a l'
  end.

(** Tests : 

Eval cbn in  LList_decomp (omega_repeat 33).
 *)


Lemma LList_decompose (A:Type) : forall l:LList A, l = LList_decomp l.
Proof.
  intros  l; now case l.
Qed.


Definition Squares_from :=
  let sqr := fun n:nat => n * n in
  (cofix F : nat -> LList nat := fun n:nat => LCons (sqr n) (F (S n))).



(** Tests :
Eval cbn in
  (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil))).
 *)

Lemma LAppend_one :
  forall (A:Type) (a:A) (u v:LList A),
    LAppend (LCons a u) v = LCons a (LAppend u v).
Proof.
  cbn in |- *.
Abort.

(** Tests : 

Eval cbn in
  (LList_decomp
     (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil )))).
 *)


Fixpoint LList_decomp_n (A:Type) (n:nat) (l:LList A) {struct n} : 
  LList A :=
  match n with
  | O => l
  | S p =>
    match LList_decomp l with
    | LNil => LNil
    | LCons a l' => LCons a (LList_decomp_n p l')
    end
  end.

(** Tests : 

Eval cbn in
  (LList_decomp_n 4
     (LAppend (LCons 1 (LCons 2 LNil)) (LCons 3 (LCons 4 LNil)))).

Eval cbn in (LList_decomp_n 12 Nats).

Eval cbn in (LList_decomp_n 5 (omega (LCons 1 (LCons 2 LNil)))).

Eval cbn in (LList_decomp (LAppend (LNil (A:=nat)) LNil)).

 Eval cbn in (LList_decomp (LAppend LNil (omega_repeat 33))). 

Eval cbn in (LList_decomp (LAppend (omega_repeat 33) (omega_repeat 69))).

 *)

Lemma LList_decompose_n (A:Type) :
  forall  (n:nat) (l:LList A), l = LList_decomp_n n l.
Proof.
  intros  n; induction n as [| n IHn]. 
  - intro l; case l; try reflexivity.
  -  intros l; case l; try trivial. 
     intros a l0; cbn in |- *; rewrite <- IHn; trivial.
Qed.

Ltac LList_unfold term := apply trans_equal with (1 := LList_decompose term).


Lemma LAppend_LNil (A:Type) : forall  v:LList A, LAppend LNil v = v.
Proof.
  intros  v; LList_unfold (LAppend LNil v). 
  case v; cbn in |- *; auto.
Qed.

Lemma LAppend_LCons (A:Type):
  forall  (a:A) (u v:LList A),
    LAppend (LCons a u) v = LCons a (LAppend u v).
Proof.
  intros  a u v; LList_unfold (LAppend (LCons a u) v).
  case v; cbn in |- *; auto.
Qed.

Hint Rewrite  LAppend_LNil LAppend_LCons : llists.

Lemma from_unfold : forall n:nat, from n = LCons n (from (S n)).
Proof.
  intro n; LList_unfold (from n); cbn in |- *; trivial.
Qed.


Lemma omega_repeat_unfold (A:Type) :
  forall a:A,
    omega_repeat a = LCons a (omega_repeat a).
Proof.
  intros  a; LList_unfold (omega_repeat a); trivial.
Qed.


Inductive Finite (A:Type) : LList A -> Prop :=
| Finite_LNil : Finite LNil
| Finite_LCons : forall (a:A) (l:LList A), Finite l -> Finite (LCons a l).

#[export] Hint Constructors  Finite: llists.

Remark one_two_three : Finite (LCons 1 (LCons 2 (LCons 3 LNil))).
Proof.
  auto with llists.
Qed.

Theorem Finite_of_LCons (A:Type) :
  forall  (a:A) (l:LList A), Finite (LCons a l) -> Finite l.
Proof.
  intros  a l H; inversion H; assumption.
Qed.


Theorem LAppend_of_Finite  (A:Type):
  forall (l l':LList A),
    Finite l -> Finite l' -> Finite (LAppend l l').
Proof.
  intros  l l' H;
    induction H; autorewrite with llists  using auto with llists.
Qed.


Lemma general_omega_LNil (A:Type) :
  forall  (u:LList A), general_omega u LNil = u.
Proof.
  intros  u; LList_unfold (general_omega u LNil).
  case u; cbn in |- *; auto.
Qed.

Lemma omega_LNil (A:Type) :  omega (LNil (A:=A)) = LNil.
Proof.
  unfold omega ; apply general_omega_LNil. 
Qed.

Lemma general_omega_LCons (A:Type) :
  forall  (a:A) (u v:LList A),
    general_omega (LCons a u) v = LCons a (general_omega u v).
Proof.
  intros  a u v;
    LList_unfold (general_omega (LCons a u) v); case v; cbn in |- *; auto.
  now  rewrite general_omega_LNil.
Qed.



Lemma general_omega_LNil_LCons (A:Type):
  forall  (a:A) (u:LList A),
    general_omega LNil (LCons a u) = LCons a (general_omega u (LCons a u)).
Proof.
  intros a u; LList_unfold (general_omega LNil (LCons a u)); trivial.
Qed.

Hint Rewrite  omega_LNil general_omega_LNil general_omega_LCons : llists.

Lemma general_omega_shoots_again  (A:Type) :
  forall (v:LList A), general_omega LNil v = general_omega v v.
Proof.
  simple destruct v. 
  -  trivial.
  -  intros; autorewrite with llists  using trivial.
     rewrite general_omega_LNil_LCons; trivial.
Qed.


Lemma general_omega_of_Finite (A:Type) :
  forall u:LList A,
    Finite u ->
    forall v:LList A, general_omega u v = LAppend u (general_omega v v).
Proof.
  simple induction 1.
  -  intros; autorewrite with llists  using auto with llists. 
     now  rewrite general_omega_shoots_again.
  -  intros; autorewrite with llists  using auto.
     rewrite H1; auto.
Qed.


Theorem omega_of_Finite (A:Type) :
  forall  u:LList A, Finite u -> omega u = LAppend u (omega u).
Proof.
  intros; unfold omega in |- *.
  apply general_omega_of_Finite; auto.
Qed.


CoInductive Infinite (A:Type) : LList A -> Prop :=
  Infinite_LCons :
    forall (a:A) (l:LList A), Infinite l -> Infinite (LCons a l).

#[export] Hint Constructors  Infinite: llists.

(* manual proof (look at from_Infinite) *)
Definition F_from :
  (forall n:nat, Infinite (from n)) -> forall n:nat, Infinite (from n).
Proof. 
  intros H n; rewrite (from_unfold n);  split; apply H.
Defined.

Print F_from.


Theorem from_Infinite_V0 : forall n:nat, Infinite (from n).
Proof (cofix H : forall n:nat, Infinite (from n) := F_from H).

(* end of manual proof *)

(* direct  proof *)
Lemma from_Infinite : forall n:nat, Infinite (from n).
Proof.
  cofix H.
  -  intro n; rewrite (from_unfold n); now split.
Qed.


Print from_Infinite.


Lemma from_Infinite_buggy : forall n:nat, Infinite (from n).
Proof.
  cofix H.
  auto with llists.
Abort.



Lemma omega_repeat_infinite (A:Type): forall  a:A, Infinite (omega_repeat a).
Proof.
  intros a; cofix H.
  rewrite (omega_repeat_unfold a);  auto with llists.
Qed.


Lemma LNil_not_Infinite (A:Type) :  ~ Infinite (LNil (A:=A)).
Proof.
  inversion 1. 
Qed.

Lemma Infinite_of_LCons (A:Type) :
  forall  (a:A) (u:LList A), Infinite (LCons a u) -> Infinite u.
Proof.
  inversion 1; assumption.
Qed.

Lemma LAppend_of_Infinite (A:Type) :
  forall  u:LList A,
    Infinite u -> forall v:LList A, Infinite (LAppend u v).
Proof.
  cofix H.
  -  simple destruct u.
     + inversion 1.
     + intros a l H0 v.
       autorewrite with llists  using auto with llists. 
       split;  apply H;  inversion H0; auto.
Qed.

Lemma Finite_not_Infinite  (A:Type):
  forall l:LList A, Finite l -> ~ Infinite l.
Proof.
  simple induction 1.
  -  unfold not in |- *; intro H0; inversion_clear H0. 
  -  unfold not at 2 ; intros a l0 H1 H2 H3; inversion H3; auto.
Qed.


Lemma Infinite_not_Finite (A:Type) :
  forall l:LList A, Infinite l -> ~ Finite l.
Proof.
  unfold not in |- *; intros l H H0.
  absurd (Infinite l); auto.
  apply Finite_not_Infinite; auto.
Qed.

Lemma Not_Finite_Infinite (A:Type):
  forall  l:LList A, ~ Finite l -> Infinite l.
Proof.
  cofix H.
  simple destruct l.
  -  intros; absurd (Finite (LNil (A:=A))); auto with llists.
  -  split;  apply H; unfold not in |- *; intro H1.
     apply H0; auto with llists.
Qed.

Lemma general_omega_infinite  (A:Type) :
  forall (a:A) (u v:LList A), Infinite (general_omega v (LCons a u)).
Proof.
  intros  a; cofix H.
  simple destruct v.
  -  rewrite general_omega_LNil_LCons; split; auto.
  -  intros a0 l; autorewrite with llists  using auto with llists.
Qed.

Lemma omega_infinite  (A:Type) :
  forall (a:A) (l:LList A), Infinite (omega (LCons a l)).
Proof.
  unfold omega;  intros; apply general_omega_infinite.
Qed.

Lemma Lappend_of_Infinite_0 (A:Type) :
  forall  u:LList A, Infinite u -> forall v:LList A, u = LAppend u v.
Proof.
  simple destruct u.
  -  intro H; inversion H.
  - intros a l H; inversion H; intros.
    rewrite LAppend_LCons.
    assert (l = LAppend l v).
Abort.


CoInductive bisimilar (A:Type) : LList A -> LList A -> Prop :=
| bisim0 : bisimilar LNil LNil
| bisim1 :
    forall (a:A) (l l':LList A),
      bisimilar l l' -> bisimilar (LCons a l) (LCons a l').

#[export] Hint Constructors  bisimilar: llists.

Lemma bisimilar_inv_1  (A:Type) :
  forall (a a':A) (u u':LList A),
    bisimilar (LCons a u) (LCons a' u') -> a = a'.
Proof.
  intros  a a' u u' H; now inversion H.
Qed.

Lemma bisimilar_inv_2 (A:Type) :
  forall  (a a':A) (u u':LList A),
    bisimilar (LCons a u) (LCons a' u') -> bisimilar u u'.
Proof.
  intros  a a' u u' H; inversion H; auto.
Qed.

Instance bisimilar_refl (A:Type) : Reflexive  (bisimilar (A:=A)).
Proof.
  cofix H.
  intros  u; case u; [ left | right ]; apply H.
Qed.


Instance bisimilar_sym (A: Type) : Symmetric  (bisimilar (A:=A)).
Proof.
  cofix H.
  intros x y; case x; case y; (left || inversion 1).
  -  right; auto.
Qed.

Instance  bisimilar_trans  (A: Type): Transitive  (bisimilar (A:=A)).
Proof.
  cofix  H; intros x y; case x, y.
  -  auto.
  -  inversion 1. 
  - inversion 1. 
  - destruct z.
    + inversion 2.
    +  intros H1 H2; inversion_clear H1; inversion_clear H2. 
       right. apply H with y;auto. 
Qed.

Instance  bisimilar_equiv (A:Type) : Equivalence (bisimilar (A:=A)).
Proof.
  split.
  - apply bisimilar_refl.   
  - apply bisimilar_sym. 
  - apply bisimilar_trans.
Qed.

Theorem bisimilar_of_Finite_is_Finite {A: Type} :
  forall l:LList A,
    Finite l -> forall l':LList A, bisimilar l l' -> Finite l'.
Proof.
  simple induction 1.
  - simple destruct l'.  
    + auto with llists.
    + inversion 1.
  -  simple destruct l'.
     + inversion 1.  
     + inversion 1; auto with llists. 
Qed.



Theorem bisimilar_of_Infinite_is_Infinite  (A:Type):
  forall l:LList A,
    Infinite l -> forall l':LList A, bisimilar l l' -> Infinite l'.
Proof.
  cofix H.
  simple destruct l.
  -  intro H0; inversion H0.
  -  simple destruct l'.
     + inversion 1.
     +  split; apply H with l0.
        *    apply Infinite_of_LCons with a;
               assumption.
        *  inversion H1; auto.
Qed.


Theorem bisimilar_of_Finite_is_eq (A: Type) :
  forall  l:LList A,
    Finite l -> forall l':LList A, bisimilar l l' -> l = l'.
Proof.
  simple induction 1.
  - intros l' H1; inversion H1; auto.
  -  simple destruct l'.
     + inversion 1.
     +  intros a0 l1 H2; inversion H2; auto with llists.
        rewrite (H1 l1); auto.
Qed.


Lemma bisimilar_LNth (A:Type):
  forall  (n:nat) (u v:LList A), bisimilar u v -> LNth n u = LNth n v.
Proof.
  simple induction n;
    simple destruct u; simple destruct v.
  -   intros; cbn in |- *; trivial.
  -   intros a l H; inversion H.
  -   intro H; inversion H.
  -   intros a0 l0 H; inversion H; cbn in |- *; trivial.
  -   intros; cbn in |- *; trivial.
  -   intros a l H0; inversion H0.
  -   intro H0; inversion H0.
  -  cbn  in |- *; auto.
     intros a0 l0 H0; inversion_clear H0;  auto.
Qed.


Lemma LNth_bisimilar  (A:Type) :
  forall u v:LList A,
    (forall n:nat, LNth n u = LNth n v) -> bisimilar u v.
Proof.
  cofix H.
  simple destruct u; simple destruct v.
  -  left.
  -  intros a l H1; generalize (H1 0); discriminate 1.
  -  intro H1; generalize (H1 0); discriminate 1.
  - intros a0 l0 H0; generalize (H0 0); cbn in |- *.
    injection 1; intro; subst a0; right.
    apply H;  intro n; generalize (H0 (S n)); auto.
Qed.

Lemma LAppend_assoc (A:Type):
  forall  (u v w:LList A),
    bisimilar (LAppend u (LAppend v w)) (LAppend (LAppend u v) w).
Proof.
  cofix H.
  simple destruct u; intros; autorewrite with llists using auto with llists.
  reflexivity.
Qed.

Lemma LAppend_of_Infinite_eq (A:Type) :
  forall  (u:LList A),
    Infinite u -> forall v:LList A, bisimilar u (LAppend u v).
Proof.
  cofix H.
  simple destruct u.
  - inversion 1.
  -  intros; autorewrite with llists using auto with llists. 
     right; apply H; now  apply Infinite_of_LCons with a.
Qed.

Lemma general_omega_lappend  (A:Type):
  forall  (u v:LList A),
    bisimilar (general_omega v u) (LAppend v (omega u)).
Proof.
  cofix H.
  simple destruct v.
  -  autorewrite with llists  using auto with llists.
     rewrite general_omega_shoots_again.
     unfold omega in |- *; auto with llists.
     intros; autorewrite with llists  using auto with llists.
     reflexivity.
  -  intros; autorewrite with llists  using auto with llists.
Qed.

Lemma omega_lappend (A:Type):
  forall  u:LList A, bisimilar (omega u) (LAppend u (omega u)).
Proof.
  intros; unfold omega at 1 in |- *; apply general_omega_lappend.
Qed.

Definition bisimulation (A:Type) (R:LList A -> LList A -> Prop) :=
  forall l1 l2:LList A,
    R l1 l2 ->
    match l1 with
    | LNil => l2 = LNil
    | LCons a l'1 =>
      match l2 with
      | LNil => False
      | LCons b l'2 => a = b /\ R l'1 l'2
      end
    end.

Theorem park_principle (A:Type) (R:LList A -> LList A -> Prop) :
  bisimulation R -> forall l1 l2:LList A, R l1 l2 -> bisimilar l1 l2. 
Proof.
  intros  bisim; cofix H.
  intros l1 l2; case l1; case l2.
  -  left.
  -  intros a l H0;  generalize (bisim _ _ H0).
     intro H1; discriminate H1.
  -  intros a l H0; generalize (bisim _ _ H0).
     contradiction.
  -  intros a l a0 l0 H0; generalize (bisim _ _ H0).
     intros [e1 H1]; subst a0; right; now  apply H.
Qed.

CoFixpoint alter  : LList bool := LCons true (LCons false alter).

Definition alter2 : LList bool := omega (LCons true (LCons false LNil)).

Definition R (l1 l2:LList bool) : Prop :=
  l1 = alter /\ l2 = alter2 \/
  l1 = LCons false alter /\ l2 = LCons false alter2.


Lemma R_bisim : bisimulation R.
Proof.
  unfold R, bisimulation in |- *.
  repeat simple induction 1.
  -  rewrite H1, H2; cbn;  split; auto.
     right; split; auto.
     rewrite general_omega_LCons. 
     unfold alter2, omega in |- *; trivial.
     rewrite general_omega_shoots_again; trivial.
  -  rewrite H1,  H2; cbn;  split; auto.
Qed.

Lemma R_useful : R alter alter2.
Proof.
  left; auto.
Qed.

Lemma final : bisimilar alter alter2.
Proof. 
  apply park_principle with R.
  -  apply R_bisim.
  -  apply R_useful.
Qed.



(* LTL operators *)

Section LTL.
  Variables (A : Type) (a b c : A).


  Definition satisfies (l:LList A) (P:LList A -> Prop) : Prop := P l.
  #[local] Hint Unfold satisfies: llists.

  Inductive Atomic (At:A -> Prop) : LList A -> Prop :=
    Atomic_intro : forall (a:A) (l:LList A), At a -> Atomic At (LCons a l).

  #[local] Hint Resolve Atomic_intro: llists.

  Inductive Next (P:LList A -> Prop) : LList A -> Prop :=
    Next_intro : forall (a:A) (l:LList A), P l -> Next P (LCons a l).

  #[local] Hint Resolve Next_intro: llists.

  Lemma Next_example : satisfies (LCons a (omega_repeat b)) (Next (Atomic (eq b))).
  Proof.
    rewrite (omega_repeat_unfold b); auto with llists. 
  Qed.


  
  
  Inductive Eventually (P:LList A -> Prop) : LList A -> Prop :=
  | Eventually_here :
      forall (a:A) (l:LList A), P (LCons a l) -> Eventually P (LCons a l)
  | Eventually_further :
      forall (a:A) (l:LList A), Eventually P l -> Eventually P (LCons a l).

  #[local] Hint Resolve Eventually_here Eventually_further: llists.


  Lemma Eventually_of_LAppend :
    forall (P:LList A -> Prop) (u v:LList A),
      Finite u ->
      satisfies v (Eventually P) -> satisfies (LAppend u v) (Eventually P).
  Proof.                       
    unfold satisfies in |- *; simple induction 1; intros;
      autorewrite with llists  using auto with llists.
  Qed.

  CoInductive Always (P:LList A -> Prop) : LList A -> Prop :=
    Always_LCons :
      forall (a:A) (l:LList A),
        P (LCons a l) -> Always P l -> Always P (LCons a l).

  
  #[local] Hint Resolve Always_LCons: llists.

  Lemma Always_Infinite :
    forall (P:LList A -> Prop) (l:LList A),
      satisfies l (Always P) -> Infinite l.
  Proof.
    intro P; cofix H.
    simple destruct l. 
    -  inversion 1.
    -   intros a0 l0 H0; split.
        apply H; auto.
        inversion H0; auto.
  Qed.


  Definition F_Infinite (P:LList A -> Prop) : LList A -> Prop :=
    Always (Eventually P).

  Lemma F_Infinite_2_Eventually (P:LList A -> Prop):
    forall  l, F_Infinite P l-> Eventually P l.
  Proof.  
    intros  l; case l;inversion 1.
    assumption.
  Qed.

  Section A_Proof_with_F_Infinite.
    
    Let w : LList A := LCons a (LCons b LNil).

    Let w_omega := omega w.

    Let P (l:LList A) : Prop := l = w_omega \/ l = LCons b w_omega.


    Remark P_F_Infinite :
      forall l:LList A, P l -> satisfies l (F_Infinite (Atomic (eq a))).
    Proof.
      unfold F_Infinite in |- *.
      cofix P_F_Infinite.
      intro l; simple destruct 1.
      -    intro eg; rewrite eg; unfold w_omega in |- *; rewrite omega_of_Finite.
           +  unfold w in |- *;  autorewrite with llists  using auto with llists.
              split.
              auto with llists.
              apply P_F_Infinite.
              unfold P in |- *; auto.
           +    unfold w in |- *; auto with llists.
      -    intro eg; rewrite eg.
           unfold w_omega in |- *; rewrite omega_of_Finite.
           +   unfold w in |- *;  rewrite LAppend_LCons; split.
               auto with llists.
               apply P_F_Infinite.
               unfold P in |- *; left.
               rewrite <- LAppend_LCons,  <- omega_of_Finite; auto with llists.
           +  unfold w;auto with llists.
    Qed.

    Lemma omega_F_Infinite : satisfies w_omega (F_Infinite (Atomic (eq a))).
    Proof.
      apply P_F_Infinite; unfold P in |- *; now left.
    Qed.
    
  End A_Proof_with_F_Infinite.

  Theorem F_Infinite_cons (P:LList A -> Prop) :
    forall  (a:A) (l:LList A),
      satisfies l (F_Infinite P) -> satisfies (LCons a l) (F_Infinite P).
  Proof.
    split.
    -  inversion H; now right.
    -  assumption.
  Qed.

  Theorem F_Infinite_consR (P:LList A -> Prop) :
    forall  (a:A) (l:LList A),
      satisfies (LCons a l) (F_Infinite P) -> satisfies l (F_Infinite P).
  Proof.
    now  inversion 1.
  Qed.

  Definition G_Infinite (P:LList A -> Prop) : LList A -> Prop :=
    Eventually (Always P).

  Lemma always_a : satisfies (omega_repeat a) (Always (Atomic (eq a))).
  Proof.
    unfold satisfies in |- *; cofix H.
    rewrite (omega_repeat_unfold a); auto with llists.
  Qed.

  Lemma LAppend_G_Infinite (P:LList A -> Prop):
    forall (u v:LList A) ,
      Finite u ->
      satisfies v (G_Infinite P) -> 
      satisfies (LAppend u v) (G_Infinite P).
  Proof.
    simple induction 1.
    -   autorewrite with llists  using auto.
    -   intros a0 l H0 H1; autorewrite with llists  using auto.
        right; now apply H1.
  Qed.

  Lemma LAppend_G_Infinite_R (P:LList A -> Prop):
    forall (u v:LList A) ,
      Finite u ->
      satisfies (LAppend u v) (G_Infinite P) -> 
      satisfies v (G_Infinite P).
  Proof.
    simple induction 1.
    -   autorewrite with llists  using auto.
    -   intros a0 l H0 H1 H2; autorewrite with llists using auto.
        rewrite LAppend_LCons in H2; inversion_clear H2.
        +   apply H1.
            inversion_clear H3.
            generalize H4; case (LAppend l v).
            *  inversion 1.  
            *  left; auto.
        +  auto.
  Qed.

End LTL.

#[export] Hint Unfold satisfies: llists.
#[export] Hint Resolve Always_LCons: llists.
#[export] Hint Resolve Eventually_here Eventually_further: llists.
#[export] Hint Resolve Next_intro: llists.
#[export] Hint Resolve Atomic_intro: llists.

(* Automata *)

Record automaton : Type := mk_auto
                             {states : Type;
                              actions : Type;
                              initial : states;
                              transitions : states -> actions -> list states}.

#[export] Hint Unfold transitions: automata.

Definition deadlock (A:automaton) (q:states A) :=
  forall a:actions A, @transitions A q a = nil.



Unset Implicit Arguments.
Set Strict Implicit.
CoInductive Trace (A:automaton) : states A -> LList (actions A) -> Prop :=
| empty_trace : forall q:states A, deadlock A q -> Trace A q LNil 
| lcons_trace :
    forall (q q':states A) (a:actions A) (l:LList (actions A)),
      In q' (transitions A q a) -> Trace A q' l -> Trace A q (LCons a l).
Set Implicit Arguments.
Unset Strict Implicit.


Section example.

  (* states *)
  Inductive st : Set :=
  | q0 : st
  | q1 : st
  | q2 : st.

  (* actions *)
  Inductive acts : Set :=
  | a : acts
  | b : acts.


  (* transitions *)
  Definition trans (q:st) (x:acts) : list st :=
    match q, x with
    | q0, a => q1 :: nil
    | q0, b => q1 :: nil
    | q1, a => q2 :: nil
    | q2, b => q2 :: q1 :: nil
    | _, _ => nil
    end.

  (* a toy automaton *)
  Definition A1 := mk_auto q0 trans.
  
  #[local] Hint Unfold A1 : core.

  Lemma no_deadlocks : forall q:states A1, ~ deadlock  A1 q.
  Proof.
    unfold deadlock in |- *; simple destruct q; intro H.
    -  absurd (transitions A1 q0 a = nil). 
       + cbn in *; discriminate.
       +  auto.
    -  absurd (transitions A1 q1 a = nil). 
       +  cbn in  *; discriminate.
       + auto.
    -  absurd (transitions A1 q2 b = nil). 
       + cbn in  *; discriminate.
       + auto.
  Qed.

  Lemma from_q1 :
    forall t:LList acts,
      Trace A1 q1 t ->
      exists t' : LList acts, Trace A1 q2 t' /\ t = LCons a t'.
  Proof.
    intros t H; inversion_clear H.
    -  case (no_deadlocks H0). 
    - generalize H0 H1; case a0; cbn in |- *.
      +  do 2 simple destruct 1.
         exists l; auto.
      +  contradiction. 
  Qed.



  Lemma from_q0 :
    forall t:LList acts,
      Trace A1 q0 t ->
      exists t' : LList acts,
        Trace A1 q2 t' /\ (t = LCons a (LCons a t') \/ t = LCons b (LCons a t')).
  Proof.
    intros t H; inversion_clear H.
    -  case (no_deadlocks H0). 
    -  generalize H0 H1; case a0; cbn in |- *.
       +  do 2 simple destruct 1.
          intro H3; case (from_q1 H3).
          intros x [H4 H5]; exists x; auto.
          rewrite H5; auto.
       +  do 2 simple destruct 1.
          intro H3; case (from_q1 H3); intros x [H4 H5].
          exists x; auto.
          rewrite H5; auto.
  Qed.

  Lemma from_q2 :
    forall t:LList acts,
      Trace A1 q2 t ->
      exists t' : LList acts,
        (Trace A1 q2 t' \/ Trace A1 q1 t') /\ t = LCons b t'.
  Proof.
    intros t H; inversion_clear H.
    -  case (no_deadlocks H0).  
    -  generalize H0 H1; case a0; cbn in |- *.
       +  contradiction.
       +  do 2 simple destruct 1.
          * exists l; auto.
          *  exists l; auto.
             rewrite H3; auto.
          * contradiction.
  Qed.

  Theorem Infinite_bs :
    forall (q:states A1) (t:LList acts),
      Trace A1 q t -> satisfies t (F_Infinite (Atomic (eq b))).
  Proof.
    cofix Infinite_bs.
    intros q; case q.
    -  intros t Ht; case (from_q0 Ht). 
       intros x [tx [ea| eb]].
       +  rewrite ea; split.
          *  case (from_q2 tx).
             intros x0 [[t2| t1] e]; rewrite e; auto with llists.
          * split.
            case (from_q2 tx).
            intros x0 [_ e]; rewrite e; auto with llists.
            apply Infinite_bs with q2; auto.
       +  rewrite eb; split.  
          *  auto with llists.
          * case (from_q2 tx).
            intros x0 [_ e]; rewrite e.
            split.
            auto with llists. 
            case e; apply Infinite_bs with q2; auto.
    -  intros t Ht; case (from_q1 Ht).
       intros x [tx e]; rewrite e.
       split.
       +  case (from_q2 tx).
          intros x0 [_ e']; rewrite e'; auto with llists.
       +  apply Infinite_bs with q2; auto.
    - intros t Ht; case (from_q2 Ht).
      intros x [[t1| t2] e]; rewrite e.  
      split.
      +  auto with llists.
      +  apply Infinite_bs with q2; auto.
      + split.
        *  auto with llists.
        *  apply Infinite_bs with q1; auto.
  Qed.

End example.

