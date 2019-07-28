Require Import Relations.

Lemma wf_inclusion :
 forall (A:Set) (R S:A -> A -> Prop),
   inclusion A R S -> well_founded S -> well_founded R.
Proof.
 intros A R S Hincl Hwf x.
  induction  x as [x IHx] using (well_founded_ind Hwf).
  constructor;  auto. 
Qed.