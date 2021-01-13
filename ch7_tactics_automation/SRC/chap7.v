
Require Export ZArith.
Require Export List.
Require Export Arith Lia.

Section bad_proof_example_for_Induction1.

  Theorem le_plus_minus' : forall n m:nat, m <= n -> n = m+(n-m).
  Proof.
    intros n m H;  induction n. 
    -   rewrite <- le_n_O_eq with (1 := H); simpl; trivial. 
    - (* dead end *) 
  Abort.

End bad_proof_example_for_Induction1.


Theorem lazy_example : forall n:nat, (S n) + 0 = S n.
Proof.
  intros n; lazy beta iota zeta delta. 
  fold plus.
  rewrite plus_0_r; reflexivity.
Qed.

#[export] Hint  Extern  4 (_ <> _) => discriminate : core.

#[export] Hint Resolve le_S_n : le_base.

Theorem auto_le_example :
  forall n m:nat, S (S (S n)) <= S (S (S m)) ->  n <= m.
Proof.
  intros n m H.
  auto with le_base.
Qed.

Lemma unprovable_le : forall n m:nat, n <= m.
Proof.
  Time auto with arith.
  Time auto with le_base arith.
Abort.

Section bad_proof_for_auto.

  Section Trying_auto.
    Variable l1 : forall n m:nat, S n <= S m -> n <= m.

    Theorem unprovable_le2 : forall n m:nat, n <= m.
    Proof.
      Time auto with arith.
      Time try (clear l1; auto with arith; fail).
    Abort.

  End Trying_auto.

End bad_proof_for_auto.

Section combinatory_logic.

  Variables (CL:Set)(App:CL->CL->CL)(S:CL)(K:CL).
  Hypotheses
    (S_rule :
       forall A B C:CL, App (App (App S A) B) C = App (App A C)(App B C))
    (K_rule :
       forall A B:CL, App (App K A) B = A).

  Hint Rewrite  S_rule K_rule : CL_rules.

  Theorem obtain_I : forall A:CL, App (App (App S K) K) A = A.
  Proof.
    intros; autorewrite with CL_rules.
    reflexivity.
  Qed.

End combinatory_logic.

Theorem example_for_subst :
  forall (a b c d:nat), a = b+c -> c = 1 -> a+b = d -> 2*a = d+c.
Proof.
  intros a b c d H H1 H2.
  subst a.
  subst.
  lazy delta [mult] iota zeta beta; 
    rewrite  plus_0_r; 
    repeat rewrite plus_assoc_reverse;
    trivial.
Qed.

Open Scope Z_scope.

Theorem ring_example1 : forall x y:Z, (x+y) * (x+y)=x*x + 2*x*y + y*y.
Proof.
  intros x y; ring.
Qed.

Definition square (z:Z) := z*z.

Theorem ring_example2 :
  forall x y:Z, square (x+y) = square x + 2*x*y + square y.
Proof.
  intros x y; unfold square; ring.
Qed.

Theorem ring_example3 : 
  (forall x y:nat, (x+y)*(x+y) = x*x + 2*x*y + y*y)%nat.
Proof.
  intros x y; ring.
Qed.

Theorem ring_example4 :
  (forall x:nat, (S x)*(x+1) = x*x + (x+x+1))%nat.
Proof.
  intro x; ring_simplify.
  trivial.
Qed.

Require Omega.

Theorem omega_example1 :
  forall x y z t:Z, x <= y <= z /\  z <= t <= x -> x = t.
Proof.
  intros x y z t H; omega.
Qed.

Theorem omega_example2 :
  forall x y:Z,
    0 <= square x -> 3*(square x) <= 2*y -> square x <= y.
Proof.
  intros x y H H0; omega.
Qed.

Theorem omega_example3 :
  forall x y:Z,
    0 <= x*x -> 3*(x*x) <= 2*y -> x*x <= y.
Proof.
  intros x y H H0; omega.
Qed.

Check (fun (X y:Z) => 0 <= X -> 3*X <= 2*y  ->  X < y).

Require Export Reals.

Open Scope R_scope.

Theorem example_for_field : forall x y:R, y <> 0 ->(x+y) / y = 1  +(x/y).
Proof.
  intros x y H; field.
  assumption.
Qed.

Require Import Lra.

Theorem example_for_Lra : forall x y:R, x-y >1 -> x - 2*y < 0 -> x > 1.
Proof.
  intros x y H H0.
  lra.
Qed.

Theorem ex_tauto1 : forall A B:Prop, A/\B->A.
Proof.
  tauto.
Qed.

Theorem ex_tauto2 : forall A B:Prop, A/\~A -> B.
Proof.
  tauto.
Qed.

Open Scope Z_scope.

Theorem ex_tauto3 : forall x y:Z, x<=y -> ~(x<=y) -> x=3.
Proof.
  tauto.
Qed.

Theorem ex_tauto4 : forall A B:Prop, A\/B -> B\/A.
Proof.
  tauto. 
Qed.

Theorem ex_tauto5 : 
  forall A B C D:Prop, (A->B)\/(A->C)->A->(B->D)->(C->D)->D.
Proof.
  tauto.
Qed.

Open Scope nat_scope.

Theorem example_intuition :
  (forall n p q:nat,  n <= p \/ n <= q -> n <= p \/ n <= S q).
Proof.
  intros n p q; intuition auto with arith.
Qed.

Ltac autoClear h := try (clear h; auto with arith; fail).

Ltac autoAfter tac := try (tac; auto with arith; fail).

Open Scope nat_scope.

Theorem example_for_autoAfter : forall  n p:nat,
    n < p -> n <= p -> 0 < p -> S n < S p.
Proof.
  intros n p H H0 H1.
  autoAfter ltac:(clear H0 H1).
Qed.

Open Scope nat_scope.

Ltac le_S_star := apply le_n || (apply le_S; le_S_star).

Theorem le_5_25 : 5 <= 25.
Proof.
  le_S_star.
Qed.

Ltac contrapose H :=
  match goal with
  | id:(~_) |- (~_) => intro H; apply id
  end.

Theorem example_contrapose : 
  forall x y:nat, x <> y -> x <= y -> ~y <= x.
Proof.
  intros x y H H0.
  contrapose H'.
  auto with arith.
Qed.



Section primes.

  Definition divides (n m:nat) := exists p:nat, p*n = m.

  Lemma divides_O : forall n:nat, divides n 0.
  Proof.
    exists 0; reflexivity.
  Qed.


  Lemma divides_plus : forall n m:nat, divides n m -> divides n (n+m).
  Proof. intros n m [q Hq]; exists (S q). subst; ring. Qed.

  Lemma not_divides_plus : forall n m:nat, ~divides n m -> ~divides n (n+m).
    intros n m H [q Hq]; apply H; red.
    destruct q.
    - exists 0. simpl in *. lia.
    -   exists q; lia.
  Qed.


  Lemma not_divides_lt : forall n m:nat, 0<m -> m<n -> ~divides n m.
  Proof.
    intros n m H H0 [q Hq].
    subst.
    destruct q.
    lia.
    cbn in H0.
    lia.
  Qed.

  Lemma not_lt_2_divides : forall n m:nat, n<>1 -> n<2 -> 0 < m -> ~ divides n m.
  Proof. 
    intros n m H H0 H1 [q Hq].
    subst.
    assert (n = 0) by lia.
    subst.
    lia.
  Qed. 


  Lemma le_plus_minus : forall n m:nat, le n m -> m = n+(m-n).
  Proof. intros; lia. Qed.


  Lemma lt_lt_or_eq : forall n m:nat, n < S m ->  n<m \/ n=m.
  Proof. inversion 1; auto.
  Qed.


  Ltac check_not_divides :=
    match goal with
    | |- (~divides ?X1 ?X2) =>
      cut (X1<=X2);[ idtac | le_S_star ]; intros Hle;
      rewrite (le_plus_minus _ _ Hle); apply not_divides_plus; 
      simpl; clear Hle; check_not_divides
    | |- _ => apply not_divides_lt; unfold lt; le_S_star

    end.
  Open Scope nat_scope.

  #[local] Hint Resolve lt_O_Sn : core.

  Ltac check_lt_not_divides :=
    match goal with
    | Hlt:(lt ?X1 2%nat) |- (~divides ?X1 ?X2) =>
      apply not_lt_2_divides; auto
    | Hlt:(lt ?X1 ?X2) |- (~divides ?X1 ?X3) =>
      elim (lt_lt_or_eq _ _ Hlt);
      [clear Hlt; intros Hlt; check_lt_not_divides
      | intros Heq; rewrite Heq; check_not_divides]
    end.

  Definition is_prime (p:nat) : Prop := 
    forall n:nat, n <> 1 -> lt n p -> ~divides n p.

  Theorem prime37 : is_prime 37.
  Proof.
    unfold is_prime; intros.
    check_lt_not_divides.
    Time Qed.

End primes.


Ltac clear_all :=
  match goal with
  | id:_ |- _ => clear id; clear_all
  | |- _ => idtac
  end.


Theorem clear_example_thm :
  forall (x y z:nat), x<z->z=2*x->0<x->x=2*y->y<z->x>y.
Proof.
  intros x y z H H1 H2 H3.
  generalize H1 H2 H3; clear_all; intros; omega.
Qed.

Theorem S_to_plus_one : forall n:nat, S n = n+1.
Proof.
  intros; rewrite plus_comm; reflexivity.
Qed.


Ltac S_to_plus_simpl :=
  match goal with
  | |-  context [(S ?X1)] =>
    match X1 with
    | 0%nat => fail 1
    | ?X2 => rewrite (S_to_plus_one X2); S_to_plus_simpl
    end
  | |- _ => idtac
  end.

Ltac a_function X1 :=
  match X1 with
  | 0%nat => fail 1
  | ?X2 => rewrite (S_to_plus_one X2); S_to_plus_simpl
  end.


Ltac simpl_on e :=
  let v := eval simpl in e in
      match goal with
      | |- context [e] => replace e with v; [idtac | auto]
      end.

Theorem simpl_on_example :
  forall n:nat, exists m : nat, (1+n) + 4*(1+n) = 5*(S m).
Proof.
  intros n; simpl_on (1+n). 
  exists n; auto with arith.
Qed.
