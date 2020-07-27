Require Import ZArith Arith Bool Omega.

Open Scope Z_scope.

(* The key to this corollary is that if s=Zsqrt_plain x, then
  s*s < (s+1) * (s+1), as stated by the companion theorem
  Zsqrt_interval, and the squaring operation is monotonic only
  for positive values. *)

Theorem div_Zsqrt :
 forall m n p:Z, 0 < m < n ->
  n=m*p-> 0 < m <= Z.sqrt n \/ 0 < p <= Z.sqrt n.
Proof.
 intros m n p Hint Heq.
 elim (Z_lt_le_dec (Z.sqrt n) m); 
 elim (Z_lt_le_dec (Z.sqrt n) p).
 -  intros Hltm Hltp.
    assert (Hlem : (Z.sqrt n)+1 <= m) by  omega.
    assert (Hlep : (Z.sqrt n)+1 <= p) by  omega.
    elim (Z.lt_irrefl n).
    apply Z.lt_le_trans with (((Z.sqrt n)+1)*((Z.sqrt n)+1)).
    assert (Hposn : 0 <= n) by  omega.
    generalize (Z.sqrt_spec n Hposn);cbv zeta;intro H23.
    intuition. 
    pattern n at 3; rewrite Heq.
    apply Zmult_le_compat; try omega.
    generalize (Z.sqrt_nonneg n).
    omega.
    generalize (Z.sqrt_nonneg n).
    omega.
 - intros Hple _; right; split; auto.
   apply Zmult_lt_0_reg_r with m; try tauto.
   rewrite Zmult_comm; omega.
 -  intros _ Hmle; left; split; tauto.
 -  intros _ Hmle; left; split; tauto.
Qed.


Definition divides_bool (p t:Z) : bool :=
 match t mod p with
   0 => true
 | _ => false
 end.

Fixpoint test_odds (n:nat) (p t:Z) {struct n} : bool :=
 match n with
 | 0%nat => negb (divides_bool 2 t)
 | S n' =>
   if test_odds n' (p - 2) t then negb (divides_bool p t) else false
 end.


Definition prime_test (n:nat) : bool :=
 match n with
 | 0%nat => false
 | 1%nat => false
 | S (S n) => 
  let x := (Z_of_nat (S (S n))) in
  let s := (Z.sqrt x) in
  let (half_s, even_bit) :=
    match s with
    | Zpos(xI h) => (Zpos h, 0)
    | Zpos(xO h) => (Zpos h, 1)
    | Zpos xH => (0, 0)
    | _ => (0, 1)  
    end  in
  test_odds (Z.abs_nat half_s) (s + even_bit) x
 end.

Time Eval lazy beta iota delta zeta in (prime_test 2333).

(* Time Eval compute in (prime_test 2333). 
 
  This command takes a much longer time.  The reason is that Z.sqrt_plain
  calls a strongly specified function, which builds a proof term that is
  large, but is discarded later.  Lazy computation avoid the useless 
  work. *)

(* we use the same axiom as in the book, it is corrected in another exercise.
 *)

Axiom verif_divide :
  (forall m p:nat, 0 < m -> 0 < p ->
   (exists q:nat, m = q*p) ->(Z_of_nat m mod Z_of_nat p = 0)%Z )%nat.

(* This axiom is actually a lemma used in the same other exercise. *)

Axiom Z_to_nat_and_back :
 forall x:Z, (0 <= x)%Z -> (Z_of_nat (Z.abs_nat x))=x.

Theorem test_odds_correct2 :
  forall n x:nat,
    (1 < x)%nat ->
  forall p:Z,
    test_odds n p (Z_of_nat x) = true ->
    ~(exists y:nat, x = y*2)%nat.
Proof.
 intros n; elim n.
 - unfold test_odds, divides_bool; intros x H1ltx _ Heq Hex.
   assert (Heq' : Z_of_nat x mod Z_of_nat 2 = 0).
  +  apply verif_divide; auto with zarith.
  +  simpl (Z_of_nat 2) in Heq'; rewrite Heq' in Heq; simpl in Heq; discriminate.

 - clear n; intros n IHn x H1ltx p; simpl.
   case_eq (test_odds n (p - 2) (Z_of_nat x)).
   +  intros Htest' _ ; apply (IHn x H1ltx (p -2)); auto.
   +  intros; discriminate.
Qed.

Theorem Z_of_nat_le :
  forall x y, Z_of_nat x <= Z_of_nat y -> (x <= y)%nat.
Proof.
 intros; omega.
Qed.


Theorem test_odds_correct :
  forall (n x:nat)(p:Z),
   p = 2*(Z_of_nat n)+1 ->
   (1 < x)%nat -> test_odds n p (Z_of_nat x) = true -> 
   forall q:nat, (1 < q <= 2*n+1)%nat -> ~(exists y:nat, x = q*y)%nat.
Proof.
 induction n.
 -  intros x p Hp1 H1ltx Hn q Hint.
    elimtype False;  omega.
  - intros x p Hp H1ltx; simpl (test_odds (S n) p (Z_of_nat x));
    intros Htest q (H1ltq, Hqle).
    case_eq (test_odds n (p -2) (Z_of_nat x)).
    + intros Htest'true.
      rewrite Htest'true in Htest.
      unfold divides_bool in Htest.
      elim (le_lt_or_eq q (2*S n + 1)%nat Hqle).
      *  intros Hqlt.
         assert (Hqle': (q <= (2* S n))%nat) by  omega.
         elim (le_lt_or_eq q (2 * S n)%nat Hqle').
         replace (2*S n)%nat with (2*n +2)%nat.
         intros Hqlt'.
         assert (Hqle'' : (q <= 2*n +1)%nat) by omega.
         apply (IHn x (p - 2)); auto with zarith arith;
         try (rewrite Hp; rewrite inj_S; unfold Z.succ); ring.
         ring.
         intros Hq (y, Hdiv); elim (test_odds_correct2 n x H1ltx (p - 2)); auto.
         exists (S n * y)%nat; rewrite Hdiv; rewrite Hq; ring.
  
      * intros Hq Hex; assert (Hp' : p = Z_of_nat q).
        rewrite Hp; rewrite Hq; rewrite inj_plus; rewrite inj_mult; auto.
        rewrite Hp' in Htest; rewrite (verif_divide x q) in Htest.
        simpl in Htest; discriminate.
        omega.
        omega.
        elim Hex; intros y Hdiv; exists y; rewrite Hdiv; ring.
    + intros Htest'; rewrite Htest' in Htest; simpl in Htest; discriminate.
Qed.

Axiom divisor_smaller :
  (forall m p:nat, 0 < m -> forall q:nat, m = q*p -> q <= m)%nat.


Theorem lt_Zpos : forall p:positive, 0 < Zpos p.
Proof.
 intros p; elim p.
 -  intros; rewrite Zpos_xI; omega.
 -  intros; rewrite Zpos_xO; omega.
 -  auto with zarith.
Qed.

Theorem Zneg_lt : forall p:positive, Zneg p < 0.
Proof.
 intros p; elim p.
 -  intros; rewrite Zneg_xI; omega.
 -  intros; rewrite Zneg_xO; omega.
 -  auto with zarith.
Qed.


Theorem prime_test_correct :
 forall n:nat, prime_test n = true ->
 ~(exists k:nat, k <> 1 /\ k <> n /\ (exists q:nat, n = q*k))%nat.
Proof.
 intros n; case_eq n.
 -  simpl;  intros Heq Hd; discriminate.
 -  intros n0; case_eq n0.
   +  simpl; intros Heq1 Heq2 Hd; discriminate.
   + unfold prime_test; intros n1 Heqn0 Heqn.
     assert (H1ltn : (1 < n)%nat).
     *  rewrite Heqn; auto with arith.
     * rewrite <- Heqn.
       lazy beta zeta delta [prime_test].
       case_eq (Z.sqrt (Z_of_nat n)).
       intros Hsqrt_eq.
       elim (Zlt_asym 1 (Z_of_nat n)).
       omega.
       lapply (Z.sqrt_spec (Z_of_nat n)).
       rewrite Hsqrt_eq; simpl.
       omega.
       omega.
       intros p Hsqrt_eq Htest_eq (k, (Hn1, (Hnn, (q,Heq)))).
       assert (H0ltn:(0 < n)%nat) by  omega.
       assert (Hkltn:(k < n)%nat).
       assert (Heq' : n=(k*q)%nat).
       rewrite Heq; ring.
       generalize (divisor_smaller n q H0ltn k Heq'). 
       omega.
       assert (Hex: exists k':nat, (1 < (Z_of_nat k') <= (Z.sqrt (Z_of_nat n))) /\
               (exists q':nat, n=(k'*q')%nat)).
       elim (div_Zsqrt (Z_of_nat k) (Z_of_nat n) (Z_of_nat q)).
       intros Hint1; exists k;split.
       omega.
       exists q; rewrite Heq; ring.
       intros Hint2; exists q; split.
       split.
       elim (Zle_or_lt (Z_of_nat q) 1); auto.
       intros hqle1;  assert (Hq1: q = 1%nat).
       omega.
       rewrite Hq1 in Heq; simpl in Heq; elim Hnn; rewrite Heq; ring.
       tauto.
       exists k; auto.
       split.
       case_eq k.
       intros Hk0; rewrite Hk0 in Heq; rewrite Heq in H1ltn;
       rewrite mult_0_r in H1ltn; omega.
       intros; unfold Z.lt; simpl; auto.
       omega.
       rewrite Zmult_comm; rewrite <- inj_mult; rewrite Heq;auto.
       elim Hex; intros k' ((H1ltk', Hk'ltsqrt), Hex'); clear Hex.
       case_eq p.
       intros p' Hp; rewrite Hp in Htest_eq.
       elim (test_odds_correct (Z.abs_nat (Zpos p'))
           n (Zpos p)) with k'.
       rewrite Z_to_nat_and_back.
       rewrite Hp.
       auto with zarith.
       auto with zarith.
       auto.
       repeat rewrite Zminus_0_r in Htest_eq.
       rewrite Hp; auto.
       split.
       omega.
       apply Z_of_nat_le.
       rewrite inj_plus.
       rewrite inj_mult.
       rewrite Z_to_nat_and_back.
       simpl (Z_of_nat 2).
       simpl (Z_of_nat 1).
       rewrite <- Zpos_xI.
       rewrite <- Hp.
       rewrite <- Hsqrt_eq; auto.
       auto with zarith.
       auto.
       intros p' Hp; rewrite Hp in Htest_eq.
       elim (test_odds_correct (Z.abs_nat (Zpos p')) n (Zpos p + 1))
       with k'.
       rewrite Z_to_nat_and_back.
       rewrite Hp; rewrite Zpos_xO; ring.
       generalize (lt_Zpos p'); intros; omega.
       auto.
       rewrite <- Hp in Htest_eq; auto.
       split; try omega.
       apply Z_of_nat_le.
       rewrite inj_plus.
       rewrite inj_mult.
       rewrite Z_to_nat_and_back.
       simpl (Z_of_nat 2); simpl (Z_of_nat 1).
       rewrite <- Zpos_xO.
       rewrite <- Hp; omega.
       auto with zarith.
       auto.
       intros Hp; rewrite Hp in Hsqrt_eq.
       rewrite Hsqrt_eq in Hk'ltsqrt.
       omega.
       intros p Hsqrt_eq.
       elim (Zle_not_lt 0 (Z.sqrt (Z_of_nat n))).
       apply Z.sqrt_nonneg.
       rewrite Hsqrt_eq.
       apply Zneg_lt.
Qed.

