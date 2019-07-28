Require Export ZArith.
Require Export Arith.


Fixpoint check_range (v:Z)(r:nat)(sr:Z){struct r} : bool :=
  match r with
    O => true
  | S r' =>
    match (v mod sr)%Z with
      Z0 => false
    | _ => check_range v r' (Z.pred sr)
    end
  end.

Definition check_primality (n:nat) :=
  check_range (Z_of_nat n)(pred (pred n))(Z_of_nat (pred n)).

Theorem verif_divide :
    forall m p:nat, 0 < m -> 0 < p ->
    (exists q:nat, m = q*p) -> (Z_of_nat m mod Z_of_nat p = 0)%Z.
Proof.
 intros m p Hltm Hltp (q, Heq); rewrite Heq.
 rewrite inj_mult.
 replace (Z_of_nat q * Z_of_nat p)%Z with (0 + Z_of_nat q * Z_of_nat p)%Z;
    try ring.
 rewrite Z_mod_plus; auto.
 omega.
Qed.

Theorem divisor_smaller :
    forall m p:nat, 0 < m -> forall q:nat, m = q*p -> q <= m.
Proof.
 intros m p Hlt; case p.
 -  intros q Heq; rewrite Heq in Hlt; rewrite mult_comm in Hlt.
     elim (lt_irrefl 0);exact Hlt.
 -  intros p' q; case q.
    +  intros Heq; rewrite Heq in Hlt.
       elim (lt_irrefl _ Hlt).
    + intros q' Heq; rewrite Heq.
      rewrite mult_comm; simpl; auto with arith.
Qed.

Theorem Zabs_nat_0 : forall x:Z, Z.abs_nat x = 0 -> (x = 0)%Z.
Proof.
 intros x; case x.
 -  simpl; auto.
 -  intros p Heq; elim (lt_irrefl 0).
    pattern 0 at 2; rewrite <- Heq.
    simpl; apply lt_O_nat_of_P.
 -  intros p Heq; elim (lt_irrefl 0).
    pattern 0 at 2; rewrite <- Heq.
    simpl; apply lt_O_nat_of_P.
Qed.

Theorem Z_to_nat_and_back :
 forall x:Z, (0 <= x)%Z -> (Z.of_nat (Z.abs_nat x))=x.
Proof.
 intros x; case x.
 - reflexivity. 
 -  intros p Hd; elim p.
   +  unfold Z.abs_nat; intros p' Hrec; rewrite nat_of_P_xI.
      rewrite inj_S,  inj_mult,  Zpos_xI.
      unfold Z.succ; rewrite Hrec;  simpl; auto.
   +  unfold Z.abs_nat; intros p' Hrec; rewrite nat_of_P_xO.
      rewrite inj_mult,  Zpos_xO.
      unfold Z.succ; rewrite Hrec; simpl; auto.
   +  simpl; auto.
 
 -  intros p' Hd; elim Hd;auto.
Qed.

Theorem  check_range_correct :
  forall (v:Z)(r:nat)(rz:Z),
  (0 < v)%Z -> Z_of_nat (S r) = rz -> check_range v r rz = true ->
  ~(exists k:nat, k <= S r /\ k <> 1 /\ 
                       (exists q:nat, Z.abs_nat v = q*k)).
Proof.
 intros v r; elim r.
 -  intros rz Hlt H1 H2 Hex; case Hex; intros k; case k.
   +  intros (Hle, (Hne1, (q, Heq))).
      rewrite mult_comm in Heq; simpl in Heq.
      rewrite (Zabs_nat_0 _ Heq) in Hlt.
      elim (Z.lt_irrefl 0); assumption.
 
   + intros k' (Hle, (Hne1, (q, Heq))).
     inversion Hle.
     *  assert (H':k'=0) by  assumption.
        rewrite H' in Hne1; elim Hne1;auto.
     *  assert (H': S k' <= 0) by  assumption.
        inversion H'.

 -  intros r' Hrec rz Hlt H1 H2 Hex; case Hex; intros k; case k.
    intros (Hle, (Hne1, (q, Heq))).
    rewrite mult_comm in Heq; simpl in Heq.
    rewrite (Zabs_nat_0 _ Heq) in Hlt.
    elim (Z.lt_irrefl 0); assumption.
    intros k' (Hle, (Hne1, (q, Heq))).
    inversion Hle.
    rewrite <- H1 in H2. 
    rewrite <- (Z_to_nat_and_back v) in H2.
    assert (Hmod:(Z.of_nat (Z.abs_nat v) mod Z.of_nat (S (S r')) = 0)%Z).
    +  apply verif_divide.
       replace 0 with (Z.abs_nat 0%Z).
       apply Zabs_nat_lt.
       omega.
       simpl; auto.
       auto with arith.
       exists q.
       assert (H': k' = S r') by  assumption.
       rewrite <- H'.
       assumption.
    +  unfold check_range in H2.
       rewrite Hmod in H2.
       discriminate H2.
      + omega.
      + unfold check_range in H2; fold check_range in H2.
        case_eq ((v mod rz)%Z).
        *  intros Heqmod; rewrite Heqmod in H2; discriminate H2.
        *  intros pmod Heqmod; rewrite Heqmod in H2;  elim (Hrec (Z.pred rz) Hlt).
           rewrite <- H1; repeat rewrite inj_S;  rewrite <- Zpred_succ; auto. 
          assumption.
          exists (S k'); repeat split;auto.
          exists q; assumption.

        * intros p Hmod; elim (Z_mod_lt v rz).
          rewrite Hmod; unfold Z.le; simpl; intros Hle'; elim Hle';auto.
          rewrite <- H1; rewrite inj_S; unfold Z.succ;
            generalize (Zle_0_nat (S r')).
          intros; omega.
Qed.

Theorem nat_of_P_Psucc : 
 forall p:positive, nat_of_P (Pos.succ p) = S (nat_of_P p).
Proof.
 intros p; elim p.
 - simpl; intros p'; rewrite nat_of_P_xO.
   intros Heq; rewrite Heq.
   rewrite nat_of_P_xI; ring.
- intros p' Heq; simpl; rewrite nat_of_P_xI; rewrite nat_of_P_xO;auto.
-  auto.
Qed.

Theorem nat_to_Z_and_back:
 forall n:nat, Z.abs_nat (Z_of_nat n) = n.
Proof.
 intros n; elim n.
 -  auto.
 - intros n'; simpl; case n'.
  +  simpl; auto.
  +  intros n''; simpl; rewrite nat_of_P_Psucc; intros Heq; rewrite Heq; auto.
Qed.

Theorem check_correct :
  forall p:nat, 0 < p -> check_primality p = true ->
  ~(exists k:nat, k <> 1 /\ k <> p /\ (exists q:nat, p = q*k)).
Proof.
 unfold lt; intros p Hle; elim Hle.
 -  intros Hcp (k, (Hne1, (Hne1bis, (q, Heq)))); rewrite mult_comm in Heq.
    assert (Hle' : k < 1).
    +  elim (le_lt_or_eq k 1); try(intuition; fail).
       apply divisor_smaller with (2:= Heq); auto.
    +  case_eq k.
       *  intros Heq'; rewrite Heq' in Heq; simpl in Heq; discriminate Heq.
       *  intros; omega.
 -  intros p' Hlep' Hrec; unfold check_primality.
    assert (H':(exists p'':nat, p' = (S p''))).
   +  inversion Hlep'.  
      *     exists 0; auto.
      *  eapply ex_intro;eauto.
   +  elim H'; intros p'' Hp''; rewrite Hp''.
      repeat rewrite <- pred_Sn.
      intros Hcr Hex;  elim check_range_correct with (3:= Hcr).
     *  rewrite inj_S; generalize (Zle_0_nat (S p'')).
        intros; omega.
     *  auto.
     *  elim Hex; intros k (Hne1, (HneSSp'', (q, Heq))); exists k.
       split.
       assert (HkleSSp'': k <= S (S p'')).
       apply (divisor_smaller (S (S p'')) q); auto with arith.
       rewrite mult_comm; assumption.
       omega.
       split.
       assumption.
       exists q; now  rewrite nat_to_Z_and_back.
Qed.
