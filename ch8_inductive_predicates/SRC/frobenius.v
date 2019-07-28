Require Export Arith.
Require Export ZArithRing.
Require Export Omega.

Theorem Frobenius_3_8 :
  forall n:nat,
    8 <= n -> exists p:nat, (exists q:nat, n = 3 * p + 5 * q).
Proof.
 intros n Hle; induction Hle as [ | m Hm IHm].
 - exists 1,  1; ring.
 -  destruct IHm as [p' [q']].
    destruct q'.
   +  
      assert (H3lep': 3 <= p') by omega.
      exists (p' - 3), 2.
      subst m.
      replace (3 * (p' - 3) + 5 * 2) 
        with    (S (3 * 3 + 3 * (p' - 3)))
        by  omega.
      rewrite <- mult_plus_distr_l.
      rewrite le_plus_minus_r; auto.
   +   exists (p'+2), q'; rewrite H;  ring.
Qed.
