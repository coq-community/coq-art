Require Export ZArith.
Require Export ZArithRing.
Require Export Zcompare.
Require Export Zwf.
Open Scope Z_scope.
 
Definition factZ_it_F (fact : Z ->  Z) (x : Z) :=
   match Z_lt_le_dec x 0 with
     left h => 0
    | right h =>
        match Z.eq_dec 0 x with   left h' => 1
                                 | right h'' => x * fact (x - 1) end
   end.
 
Fixpoint iter {A : Type} (f : A ->  A) (k : nat) (a : A) {struct k} : A :=
 match k with   0%nat => a
               | S p => f (iter f p a) end.
 
 
Definition factZ_terminates:
 forall (x : Z),
  ({v : Z |
   exists p : nat ,
   forall k, forall g, (p < k)%nat ->  iter factZ_it_F k g x = v }).
Proof. 
 induction  x as [x IHx] using (well_founded_induction (Zwf_well_founded 0)).
 unfold factZ_it_F;case_eq (Z_lt_le_dec x 0).
 - intros h heq1; exists 0, 1%nat.
   intros k; case k.
   + intros; omega.
   + intros; simpl; rewrite heq1; auto.
 - intros h heq2; case_eq (Z.eq_dec 0 x).
   + intros h' heq3; exists 1, 1%nat.
   intros k; case k.
     * intros; omega.
     * intros; simpl; rewrite heq2;  simpl in heq3; rewrite heq3; auto.
   + intros h'' heq4; assert (HZwf: Zwf 0 (x - 1) x).
     * clear heq2 heq4; unfold Zwf; omega.
      * destruct (IHx (x - 1) HZwf) as [v Hex]; exists (x * v).
        destruct Hex as [p Heq]; exists (S p); intros k; case k.
         intros; omega.
         simpl; intros k' hltk g; rewrite heq2; simpl in heq4;rewrite heq4.
         fold factZ_it_F;  rewrite Heq; [reflexivity | omega].  
Qed.
 
Definition factZ_it : Z ->  Z :=
   fun x =>
      match factZ_terminates x with exist _ v _ => v end.
 
Theorem factZ_fix_eqn:
 forall x,
  factZ_it x =
  match Z_lt_le_dec x 0 with
   | left h => 0
   | right h =>
       match Z.eq_dec 0 x with   left h' => 1
                                | right h'' => x * factZ_it (x - 1) end
  end.
 Proof. 
  intros x; unfold factZ_it;
  destruct  (factZ_terminates x) as [v [p Heq]];
  destruct (factZ_terminates (x - 1)) as [v' [p' Heq']].
  rewrite <- (Heq (S ((p + p') + 1)) factZ_it).
  - simpl iter; unfold factZ_it_F.
    case (Z_lt_le_dec x 0); auto.
    case (Z.eq_dec 0 x); auto.
    rewrite <- (Heq' ((p + p') + 1)%nat factZ_it).
    +  reflexivity.
    +  omega.
  - omega.
Qed.


