(**
    The "classical" definition of well-foundedness

  Pierre Casteran

 keywords :  well-founded relations, classical logic, axiom of choice

 *)

Require Import Relations.

(** 
  Please consider the usual mathematical definition of well-founded relations :
 *)



Definition classic_wf {A}(R: relation A) :=
  ~ exists (s: nat-> A),  forall i,  R (s (S i)) (s i).

(** Prove that Coq's  definition entails the classical one *)

Theorem wf_classic_wf {A} (R: relation A) : well_founded R -> classic_wf R.
Proof.
  intros HR  [s Hs].
  assert (forall x:A,  ~ exists i,  s i = x).
  {
    apply (well_founded_induction  HR).
    intros x Hx [i Hi].
    subst x;  specialize (Hs i).
    specialize (Hx _ Hs).
    apply Hx ; now exists (S i).
  }
  apply (H (s 0));  now exists 0.
Qed.


(** Now, we work with some axioms (assumed in the following libraries) *)

Require Import Classical ClassicalChoice.


(** In the current context, prove that the classical definition entails Coq's *)


Section Classic_OK_R.
  Variable (A:Type)(R: relation A).

  Hypothesis H : classic_wf R.

  Section Proof_by_absurd.

    Hypothesis (H0: ~ well_founded R).

    Lemma not_acc_ex : exists a:A,  ~ Acc R a.
    Proof.
      now apply not_all_ex_not.
    Qed.


    Lemma next_not_acc : forall a,  ~ Acc R a ->
                                    exists b,  R b a /\ ~ Acc R b.
    Proof.
      intros a H1;  apply not_all_not_ex.
      intros H2; apply H1.
      split; intros y H3.
      specialize (H2 y); apply not_and_or in H2.
      destruct H2;auto.
      -  contradiction.
      -  now apply NNPP in H2.
    Qed.

    (* In order to apply choice, we use an auxiliary sig type *)

    Let B : Type := {a : A | ~ Acc R a}. 

    Let R1 : relation B :=
      fun x y => R (proj1_sig y) (proj1_sig x).

        
    Lemma next_not_acc_R1 : forall x:B, exists y:B, R1 x y.
    Proof.
      destruct x as [a Ha].                                
      destruct (next_not_acc a Ha) as [y [Hy Hy1]].
      now exists (exist _ y Hy1).
    Qed.

        
    Fixpoint iterate {B} (f : B -> B) b n : B :=
      match n with 0 => b | S p => f (iterate f b p) end.

    Lemma L : exists f: nat -> B, forall i, R1 (f i) (f (S i)).
    Proof.
      destruct not_acc_ex as [x H1].
      destruct (choice _ next_not_acc_R1) as [h H2].
      exists (iterate h (exist _ x H1)).
      induction i; simpl; auto.
    Qed.


    Lemma L2: exists g : nat -> A, forall i, R (g (S i)) (g i).
    Proof.
      destruct L as [f Hf].
      exists (fun i =>  proj1_sig (f i)).
      intro; apply Hf.
    Qed.

    Lemma FF : False.
    Proof.
      apply H, L2.
    Qed.

  End Proof_by_absurd.

End Classic_OK_R.

Theorem classic_wf_wf  {A} (R: relation A) : classic_wf R -> well_founded R.
Proof.
  intros; apply NNPP.
  intro; now apply (FF _ R).
Qed.
  


Arguments classic_wf_wf {A}.

Print Assumptions classic_wf_wf.

(*

Axioms:
relational_choice : forall (A B : Type) (R : A -> B -> Prop),
                    (forall x : A, exists y : B, R x y) ->
                    exists R' : A -> B -> Prop, subrelation R' R /\ (forall x : A, exists ! y : B, R' x y)
dependent_unique_choice : forall (A : Type) (B : A -> Type) (R : forall x : A, B x -> Prop),
                          (forall x : A, exists ! y : B x, R x y) ->
                          exists f : forall x : A, B x, forall x : A, R x (f x)
classic : forall P : Prop, P \/ ~ P

*)

Print Assumptions wf_classic_wf.

(*

Closed under the global context
*)

