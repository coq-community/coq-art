Require Export Arith.
Require Export ArithRing.
Require Export Omega.
 
Ltac CaseEq f := generalize (refl_equal f); 
    pattern f at -1 in |- *; case f.
 
Fixpoint div4 (n:nat) : nat * nat :=
  match n with
  | S (S (S (S p))) => let (q, r) := div4 p in (S q, r)
  | a => (0, a)
  end.

Fixpoint bsqrt (n b:nat) {struct b} : nat * nat :=
  match b with
  | O => (0, 0)
  | S b' =>
      match div4 n with
      | (O, O) => (0, 0)
      | (O, S p) => (1, p)
      | (q, r0) =>
          let (s', r') := bsqrt q b' in
          match le_gt_dec (4 * s' + 1) (4 * r' + r0) with
          | left _ => (2 * s' + 1, 4 * r' + r0 - (4 * s' + 1))
          | right _ => (2 * s', 4 * r' + r0)
          end
      end
  end.

(* We start by proving a few basic properties of division by 4.
  As suggested in section 8.3.1, we can use a specific induction
  principle to work on div4.  This is also the solution to exercise
  \ref{quadruple_induction}. *)
 
Theorem div4_ind :
 forall P:nat -> Prop,
   P 0 ->
   P 1 ->
   P 2 ->
   P 3 -> (forall n:nat, P n -> P (S (S (S (S n))))) -> forall n:nat, P n.
Proof.
 intros P P0 P1 P2 P3 Prec n.
 cut (P n /\ P (S n) /\ P (S (S n)) /\ P (S (S (S n)))).
 -  intuition.
 -  elim n; intuition.
Qed.

(* Proving the main characteristics of div4 is easy using
  div4_ind.  We avoid using Simpl so that multiplications
  do not get unfolded into additions. *)
 
Lemma div4_exact : forall n:nat, let (q, r) := div4 n in n = 4 * q + r.
Proof.
 intros n; elim n using div4_ind; try (simpl in |- *; auto; fail).
 intros p; cbv beta iota zeta delta [div4] in |- *; fold div4 in |- *.
 case (div4 p).
 intros q r Hrec; rewrite Hrec; ring.
Qed.
(* Since 4 is a constant, we can use div4_exact to
   obtain a linear equality in the sense of Presburger arithmetic
  and the Omega decision procedure can cope with the formula.*)
 
Theorem div4_lt : forall n:nat, let (q, r) := div4 n in 0 < q -> q < n.
Proof.
 intros n; generalize (div4_exact n); case (div4 n).
 intros q r Heq; omega.
Qed.
 
Theorem div4_lt_rem : forall n:nat, let (q, r) := div4 n in r < 4.
Proof.
 intros n; elim n using div4_ind; try (simpl in |- *; auto with arith).
 intros p; case (div4 p); auto.
Qed.

Ltac remove_minus :=
  match goal with
  |  |- context [(?X1 - ?X2 + ?X3)] =>
      rewrite <- (plus_comm X3); remove_minus
  |  |- context [(?X1 + (?X2 - ?X3) + ?X4)] =>
      rewrite (plus_assoc_reverse X1 (X2 - X3)); remove_minus
  |  |- context [(?X1 + (?X2 + (?X3 - ?X4)))] =>
      rewrite (plus_assoc X1 X2 (X3 - X4))
  |  |- (_ = ?X1 + (?X2 - ?X3)) =>
      apply (fun n m p:nat => plus_reg_l m p n) with X3;
       try rewrite (plus_permute X3 X1 (X2 - X3)); 
       rewrite le_plus_minus_r
  end.

(* The proof of this goal is a simple matter of computation, but
   NatRing can't cope with it because of the irregular behavior of
   minus.  The tactic remove_minus defined above takes care of that by
   adding the subtracted term on both side of the equality, and then
   simplifying with le_plus_minus.  This simplification only works
   because the theorem has the right hypothesis.  *)
 
Theorem bsqrt_exact_lemma_le :
 forall n q r s' r':nat,
   n = 4 * q + r ->
   q = s' * s' + r' ->
   4 * s' + 1 <= 4 * r' + r ->
   n = (2 * s' + 1) * (2 * s' + 1) + (4 * r' + r - (4 * s' + 1)).
Proof.
 intros; remove_minus.
 subst; ring.
 assumption.
Qed.
 
Lemma bsqrt_exact_lemma_gt :
 forall n q r s' r':nat,
   n = 4 * q + r ->
   q = s' * s' + r' ->
   4 * s' + 1 > 4 * r' + r -> n = 2 * s' * (2 * s') + (4 * r' + r).
Proof.
 intros; subst; ring.
Qed.

Theorem bsqrt_exact :
 forall b n:nat, n <= b -> let (s, r) := bsqrt n b in n = s * s + r.
Proof.
 (* Induction on the bound, as should always be the case
   for bounded recursive functions. *)
 intros b; elim b.

(* When the bound is zero, if n is lower than the bound, it
  is also 0, it is only a matter of computation to check the
  equality. *)
 intros n Hle; rewrite <- (le_n_O_eq _ Hle); simpl in |- *; auto.

 (*We limit simplification to the bsqrt function. *)
 intros b' Hrec n Hle; cbv beta iota zeta delta [bsqrt] in |- *;
  fold bsqrt in |- *.

 (* We use the lemmas on div4.  To avoid CaseEq, we rely on
   Generalize before doing a Case analysis. *)
 generalize (div4_lt n) (div4_exact n).
 case (div4 n).
 intros q r; case q.
 -  case r; intros; subst; ring.
 -  intros q' Hlt Heq; generalize (Hrec (S q')); case (bsqrt (S q') b').
    intros s' r' Hrec'.

 (* Because le_gt_dec is a well-specified function,
   there is no need to generalize hypotheses to perform
  the case analysis on this function call. *)
    case (le_gt_dec (4 * s' + 1) (4 * r' + r)).
    apply bsqrt_exact_lemma_le with (S q'); auto; omega.
    apply bsqrt_exact_lemma_gt with (S q'); auto; omega.
Qed.
 
Theorem bsqrt_rem :
 forall b n:nat, n <= b -> 
   let (s, r) := bsqrt n b in n < (s + 1) * (s + 1).
Proof.
 intros b; elim b.
 -  intros n Hle; rewrite <- (le_n_O_eq _ Hle); 
  simpl in |- *; auto with arith.

 (*We limit simplification to the bsqrt function. *)
 -  intros b' Hrec n Hle; generalize (bsqrt_exact (S b') n Hle);
    cbv beta iota zeta delta [bsqrt] in |- *; fold bsqrt in |- *.

(* We use the lemmas on div4.  To avoid CaseEq, we rely on
  Generalize before doing a Case analysis. *)
 generalize (div4_lt n) (div4_exact n) (div4_lt_rem n).
 case (div4 n);  intros q r;  case q.
 + case r; intros; subst; simpl in |- *; auto with arith.
 +  intros q' Hlt Heq Hlt_rem; generalize (Hrec (S q')).
    case (bsqrt (S q') b').
    intros s' r' Hrec'.

 (* Because le_gt_dec is a well-specified function,
   there is no need to generalize hypothesese to perform
   the case analysis on this function call. *)
 case (le_gt_dec (4 * s' + 1) (4 * r' + r)).
 *  intros Hle' Heq'; rewrite Heq.
    apply lt_le_trans with (4 * S q' + 4).
    auto with arith.
     replace ((2 * s' + 1 + 1) * (2 * s' + 1 + 1)) with
     (4 * ((s' + 1) * (s' + 1))).
     abstract omega.
     ring.
 *  intros Hgt Heq'; rewrite Heq'.
    match goal with
      |  |- (?X1 < ?X2) => ring_simplify X1; ring_simplify X2
    end.
    abstract omega.
Qed.
 

Definition sqrt_nat :
  forall n:nat,
    {s : nat &  {r : nat | n = s * s + r /\ n < (s + 1) * (s + 1)}}.
 intros n; 
  generalize (bsqrt_exact n n (le_n n)) (bsqrt_rem n n (le_n n));
  case (bsqrt n n).
 intros s r H1 H2; exists s; exists r; auto.
Defined.

Example test : bsqrt 37 37 = (6,1).
Proof. reflexivity.  Qed.

Example test2 : bsqrt 49 49 = (7,0).
Proof. reflexivity.  Qed.

