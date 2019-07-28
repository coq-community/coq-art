Require Export Arith.
Require Export ArithRing.
Require Export Omega.
Require Export Compare_dec.
Require Export Wf_nat.
 
Definition div4_spec:
 forall (n : nat),  ({q : nat & {r : nat | n = 4 * q + r /\ r < 4}}).
refine (fix
        div4_spec (n : nat) : {q : nat & {r : nat | n = 4 * q + r /\ r < 4}} :=
           match n return {q : nat & {r : nat | n = 4 * q + r /\ r < 4}} with
              S (S (S (S x'))) =>
                match div4_spec x' with existT _ q' (exist _ r' H) => _ end
             | _ => _
           end); clear div4_spec.
- exists 0, 0; omega.
- exists 0, 1; omega.
- exists 0, 2; omega.
- exists 0,  3; omega.
- exists (S q'), r'; omega.
Qed.
 
Definition sqrt_nat_F:
 forall n,
 (forall y,
  y < n ->  ({s : nat & {r : nat | y = s * s + r /\ y < (s + 1) * (s + 1)}})) ->
  ({s : nat & {r : nat | n = s * s + r /\ n < (s + 1) * (s + 1)}}).
refine (fun n sqrt_nat =>
           match div4_spec n with
             existT _ 0 (exist _ 0 (conj Heq _)) => _
            | existT _ 0 (exist _ (S r') (conj Heq Hle)) => _
            | existT _ (S q') (exist _ r' (conj Heq Hle)) => _
           end).
- clear sqrt_nat;exists 0, 0; omega.
- exists 1, r';rewrite Heq; split.
  + ring.
  + omega.
 - assert (Hlt: S q' < n) by omega.
   destruct (sqrt_nat (S q') Hlt) as [s' [r'' [Heq' Hlt']]].
   case (le_lt_dec (4 * s' + 1) (4 * r'' + r')).
   + intros Hle'';
     exists (2 * s' + 1), ((4 * r'' + r') - (4 * s' + 1)).
    rewrite Heq,  Heq'; split.
    * replace ((2 * s' + 1) * (2 * s' + 1) + ((4 * r'' + r') - (4 * s' + 1)))
     with (4 * (s' * s') + ((4 * s' + 1) + ((4 * r'' + r') - (4 * s' + 1)))).
     rewrite le_plus_minus_r; [ring | assumption].
     ring.
    * replace (4 * (s' * s' + r'') + r') with ((4 * s') * s' + (4 * r'' + r')).
      replace (((2 * s' + 1) + 1) * ((2 * s' + 1) + 1))
      with ((4 * s') * s' + (8 * s' + 4)).
      apply plus_lt_compat_l.
      assert (H: r'' < 2 * s' + 1).
      { apply plus_lt_reg_l with (s' * s').
        rewrite <- Heq'.
        replace (s' * s' + (2 * s' + 1)) with ((s' + 1) * (s' + 1)).
        assumption.
        ring.
      }
      omega.
      ring.
      ring.
   + intros Hlt''; exists (2 * s'),  (4 * r'' + r');
     rewrite Heq,  Heq'.
     split.
     * ring.
     * replace (4 * (s' * s' + r'') + r') with ((4 * s') * s' + (4 * r'' + r')).
       replace ((2 * s' + 1) * (2 * s' + 1)) with ((4 * s') * s' + (4 * s' + 1)).
       omega.
       ring.
       ring.
Qed.
 
Definition sqrt_nat' :
  forall n,  ({s : nat & {r : nat | n = s * s + r /\ n < (s + 1) * (s + 1)}}) :=
   well_founded_induction
    lt_wf
    (fun n => {s : nat & {r : nat | n = s * s + r /\ n < (s + 1) * (s + 1)}})
    sqrt_nat_F.
