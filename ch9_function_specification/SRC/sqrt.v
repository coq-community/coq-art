Require Export ZArith.
Require Export ZArithRing Extraction.
Open Scope Z_scope.

(* The specification given in the exercise is rather cumbersome, because
  it requires formula that are outside Presburger arithmetic.  We make a
  detour using a more practical specification. *)

Definition sqrt_type2 :=
  fun v s r => (Zpos v) = s*s+r /\ 0 <= r <= 2*s.

Definition sqrt_type1 :=
  fun p s => {r:Z | sqrt_type2 p s r}.

Theorem th_sqrt1 : 1=1*1+0 /\ 0<= 0 <= 2*1.
Proof.
 simpl;auto with zarith.
Qed.

Theorem th_sqrt2 : 2=1*1+1 /\ 0 <= 1 <= 2*1.
Proof.
 simpl; auto with zarith.
Qed.

Theorem th_sqrt3 : 3=1*1+2 /\ 0 <= 2 <= 2*1.
Proof.
 simpl; auto with zarith.
Qed.

Theorem th_sqrt_4_0_le :
   forall p s r,
     Zpos p = s*s+r /\ 0<= r <= 2*s ->
     4*s+1 <= 4*r ->
     Zpos(xO (xO p)) = (2*s+1)*(2*s+1)+(4*r - (4*s+1)) /\
     0<= 4*r-(4*s+1) <= 2*(2*s+1).
Proof.
 intros p s r [Heq Hlt] Hle; rewrite Zpos_xO; rewrite (Zpos_xO p).
 rewrite Heq;  split.
 - ring.
 - split; omega.
Qed.
  
Theorem th_sqrt_4_0_gt :
   forall p s r,
     Zpos p = s*s+r /\ 0<= r <= 2*s ->
     4*s+1 > 4*r ->
     Zpos(xO (xO p)) = (2*s)*(2*s)+4*r /\
     0<= 4*r <= 2*(2*s).
Proof.
 intros p s r [Heq Hlt] Hle; rewrite Zpos_xO; rewrite (Zpos_xO p).
 rewrite Heq; split.
 -  ring.
 -  split; omega.
Qed.
  
Theorem th_sqrt_4_2_le :
   forall p s r,
     Zpos p = s*s+r /\ 0<= r <= 2*s ->
     4*s+1 <= 4*r+2 ->
     Zpos(xO (xI p)) = (2*s+1)*(2*s+1)+(4*r+2-(4*s+1)) /\
     0<= (4*r+2)-(4*s+1) <= 2*(2*s+1).
Proof.
 intros p s r [Heq Hlt] Hle; rewrite Zpos_xO; rewrite (Zpos_xI p).
 rewrite Heq; split.
 -  ring.
 -  split; omega.
Qed.
  
Theorem th_sqrt_4_2_gt :
   forall p s r,
     Zpos p = s*s+r /\ 0<= r <= 2*s ->
     4*s+1 > 4*r+2 ->
     Zpos(xO (xI p)) = (2*s)*(2*s)+(4*r+2) /\
     0<= 4*r+2 <= 2*(2*s).
Proof.
 intros p s r [Heq Hlt] Hle; rewrite Zpos_xO; rewrite (Zpos_xI p).
 rewrite Heq; split.
 -  ring.
 -  split; omega.
Qed.
  
Theorem th_sqrt_4_1_le :
   forall p s r,
     Zpos p = s*s+r /\ 0<= r <= 2*s ->
     4*s+1 <= 4*r+1 ->
     Zpos(xI (xO p)) = (2*s+1)*(2*s+1)+(4*r+1-(4*s+1)) /\
     0<= (4*r+1)-(4*s+1) <= 2*(2*s+1).
Proof.
 intros p s r [Heq Hlt] Hle; rewrite Zpos_xI; rewrite (Zpos_xO p).
 rewrite Heq; split.
 -  ring.
 -  split; omega.
Qed.
  
Theorem th_sqrt_4_1_gt :
   forall p s r,
     Zpos p = s*s+r /\ 0<= r <= 2*s ->
     4*s+1 > 4*r+1 ->
     Zpos(xI (xO p)) = (2*s)*(2*s)+(4*r+1) /\
     0<= 4*r+1 <= 2*(2*s).
Proof.
 intros p s r [Heq Hlt] Hle; rewrite Zpos_xI; rewrite (Zpos_xO p).
 rewrite Heq;  split.
 -  ring.
 -  split; omega.
Qed.
  
Theorem th_sqrt_4_3_le :
   forall p s r,
     Zpos p = s*s+r /\ 0<= r <= 2*s ->
     4*s+1 <= 4*r+3 ->
     Zpos(xI (xI p)) = (2*s+1)*(2*s+1)+(4*r+3-(4*s+1)) /\
     0<= (4*r+3)-(4*s+1) <= 2*(2*s+1).
Proof.
 intros p s r [Heq Hlt] Hle; rewrite Zpos_xI; rewrite (Zpos_xI p).
 rewrite Heq;  split.
 -  ring.
 -  split; omega.
Qed.
  
Theorem th_sqrt_4_3_gt :
   forall p s r,
     Zpos p = s*s+r /\ 0<= r <= 2*s ->
      4*s+1 > 4*r+3 ->
     Zpos(xI (xI p)) = (2*s)*(2*s)+(4*r+3) /\
     0<= 4*r+3 <= 2*(2*s).
Proof.
 intros p s r [Heq Hlt] Hle; rewrite Zpos_xI; rewrite (Zpos_xI p).
 rewrite Heq;  split.
 -  ring.
 -  split; omega.
Qed.
  
Fixpoint sqrt_aux (p:positive) :
  {s:Z &{r:Z | Zpos p = s*s+r /\ 0 <= r <= 2*s}} :=
match p return {s:Z & (sqrt_type1 p s)} with
  1%positive => existT (sqrt_type1 1) 1 (exist (sqrt_type2 1 1) 0 th_sqrt1)
| 2%positive => existT (sqrt_type1 2) 1 (exist (sqrt_type2 2 1) 1 th_sqrt2)
| 3%positive => existT (sqrt_type1 3) 1 (exist (sqrt_type2 3 1) 2 th_sqrt3)
| xO (xO p') =>
  match sqrt_aux p' with
    (existT _ s' (exist _ r' h)) =>
    match Z_le_gt_dec  (4*s'+1) (4*r') with
      left h' =>
        (existT  (sqrt_type1 (xO (xO p'))) (2*s'+1)
           (exist  (sqrt_type2 (xO (xO p')) (2*s'+1)) ((4*r')-(4*s'+1)) 
                (th_sqrt_4_0_le p' s' r' h h')))
    | right h' =>
        (existT (sqrt_type1 (xO (xO p'))) (2*s')
           (exist (sqrt_type2 (xO (xO p')) (2*s')) (4*r') 
                (th_sqrt_4_0_gt p' s' r' h h')))
    end
  end
| xO (xI p') =>
  match sqrt_aux p' with
    (existT _ s' (exist _ r' h)) =>
    match Z_le_gt_dec  (4*s'+1) (4*r'+2) with
      left h' =>
        (existT (sqrt_type1 (xO (xI p'))) (2*s'+1)
           (exist (sqrt_type2 (xO (xI p')) (2*s'+1))
              ((4*r'+2)-(4*s'+1)) (th_sqrt_4_2_le p' s' r' h h')))
    | right h' =>
        (existT (sqrt_type1 (xO (xI p'))) (2*s')
           (exist (sqrt_type2 (xO (xI p')) (2*s'))
              (4*r'+2) (th_sqrt_4_2_gt p' s' r' h h')))
    end
  end
| xI (xO p') =>
  match sqrt_aux p' with
    (existT _ s' (exist _ r' h)) =>
    match Z_le_gt_dec  (4*s'+1) (4*r'+1) with
      left h' =>
        (existT (sqrt_type1 (xI (xO p'))) (2*s'+1)
           (exist (sqrt_type2 (xI (xO p')) (2*s'+1))
             ((4*r'+1)-(4*s'+1)) (th_sqrt_4_1_le p' s' r' h h')))
    | right h' =>
        (existT (sqrt_type1 (xI (xO p'))) (2*s')
           (exist (sqrt_type2 (xI (xO p')) (2*s')) (4*r'+1) 
              (th_sqrt_4_1_gt p' s' r' h h')))
    end
  end
| xI (xI p') =>
  match sqrt_aux p' with
    (existT _ s' (exist _ r' h)) =>
    match Z_le_gt_dec  (4*s'+1) (4*r'+3) with
      left h' =>
        existT (sqrt_type1 (xI (xI p'))) (2*s'+1)
           (exist (sqrt_type2 (xI (xI p')) (2*s'+1))
               ((4*r'+3)-(4*s'+1)) (th_sqrt_4_3_le p' s' r' h h'))
    | right h' =>
        existT (sqrt_type1 (xI (xI p'))) (2*s')
           (exist (sqrt_type2 (xI (xI p')) (2*s'))
              (4*r'+3) (th_sqrt_4_3_gt p' s' r' h h'))
    end
  end
end.

(* We must now fulfill the required specification. *)

Definition sqrt :
  forall p, {s:Z &{r:Z | Zpos p = s*s+r /\ s*s <= Zpos p < (s+1)*(s+1)}}.
Proof. 
 intros p; case (sqrt_aux p); intros s [r [Heq [H0_le_r Hr_le_2s]]].
 exists s; exists r;split.
 - exact Heq.
 - split.
   + omega.
   + replace ((s+1)*(s+1)) with (s*s + 2*s +1).
     * omega.
     * ring.
Defined.

Recursive Extraction sqrt.