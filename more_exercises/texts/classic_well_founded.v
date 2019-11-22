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
Admitted.

(** Now, we work with some axioms (assumed in the following libraries) *)

Require Import Classical ClassicalChoice.



(** In the current context, prove that the classical definition entails Coq's 
    (you may apply the following theorem)  *)

About choice.

Print Assumptions choice.


Theorem classic_wf_wf {A} (R: relation A) : classic_wf R -> well_founded R.
Proof.
Admitted.



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








  
