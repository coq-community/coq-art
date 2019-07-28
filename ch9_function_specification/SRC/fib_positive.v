Require Export Arith.
Require Export ArithRing.
Require Export ZArith.
Require Import fib_ind.

Theorem fib_n_p :
  forall n p, fib (n + p + 2) =
             fib (n + 1) * fib (p + 1) + fib n * fib p. 
Proof.
  intros n; elim n using fib_ind.
  -   intros p; replace (0 + p+2) with (S (S p)) by ring.
      replace (p+1) with (S p) by ring.
      rewrite fib_SSn; simpl; ring.
  -   intros p; replace (1+p+2) with (S (S (S p))) by ring.
      simpl (fib (1+1));  simpl (fib 1).
      replace (p+1) with (S p) by ring.
      repeat rewrite fib_SSn; ring.
  -  intros n' IHn' IHn'1 p.
     replace (S (S n') + p + 2) with (S (S (n'+p + 2))) by ring.
     simpl (S (S n') + 1);  repeat rewrite fib_SSn.
     replace (S (n'+p+2)) with (S n' +p+2) by ring.
     rewrite IHn'1,  IHn'.
     replace (S n'+1) with (S (S n')) by ring.
     replace (S (n'+1)) with (S (S n')) by ring.
     rewrite fib_SSn; ring.
Qed.

Theorem fib_monotonic :  forall n, fib n <= fib (n+1).
Proof.
 intros n; elim n using fib_ind; auto with arith.
 intros n' H1 H2; replace (S (S n')+1) with (S (S (S n'))) by ring.
 rewrite (fib_SSn (S n')); auto with arith.
Qed.

Theorem fib_n_p' :
  forall n p, fib (n + p) =
     fib n * fib p + (fib (n+1) - fib n)  *(fib (p+1) - fib p).
Proof.
 intros n; induction n as [ | | n IHn IHSn]  using fib_ind.
 -  intros p; simpl; ring.
 -  intros p; replace (1 + p) with (p + 1) by ring; simpl.  
   ring_simplify.
   rewrite le_plus_minus_r.
   + reflexivity.  
   + apply fib_monotonic.
 -  intro p; simpl (S (S n) + p);rewrite fib_SSn.
    replace (S (n + p)) with (S n + p) by ring.
    rewrite IHn, IHSn; simpl (S (S n)+1).
    replace (S n + 1) with (S (S n)) by ring.
    replace (S (n + 1)) with (S (S n)) by ring.
    repeat rewrite fib_SSn.
    rewrite (plus_comm (fib (S n))
             (fib n + fib (S n))).
    rewrite minus_plus.
    rewrite (plus_comm (fib n) (fib (S n))).
    rewrite minus_plus.
    rewrite mult_minus_distr_r.
    replace
   (fib n * fib p +
   (fib (n + 1) * (fib (p + 1) - fib p) - fib n * (fib (p + 1) - fib p)) +
   (fib (S n) * fib p + fib n * (fib (p + 1) - fib p)))
  with
   (fib n * fib p +
   (fib n * (fib (p + 1) - fib p) +
   (fib (n + 1) * (fib (p + 1) - fib p) - 
         fib n * (fib (p + 1) - fib p))) +   fib (S n) * fib p) by ring.
    rewrite (le_plus_minus_r).
    replace (n + 1) with (S n) by ring.
    ring.
    apply mult_le_compat_r.
    apply fib_monotonic.
Qed.

Theorem fib_2n :
  forall n, fib (2*n) = fib (n) * fib (n) + 
           (fib (n+1) - fib n)*(fib (n+1) - fib n).
Proof.
 intros n; replace (2*n) with (n+n) by ring.
 apply fib_n_p'.
Qed.

Theorem fib_2n_plus_1 :
  forall n, fib (2*n+1) = 2 * fib n * fib (n+1) - fib n * fib n.
Proof.
 intros n; replace (2*n+1) with (n + (n + 1)) by ring.
 rewrite fib_n_p'.
 replace (n + 1 + 1) with (S (S n)) by ring.
 rewrite fib_SSn.
 replace (S n) with (n + 1) by ring.
 rewrite (plus_comm (fib n) (fib (n + 1))).
 rewrite minus_plus.
 apply plus_reg_l with (fib n * fib n).
 rewrite le_plus_minus_r.
 rewrite plus_permute.
 rewrite mult_minus_distr_r.
 rewrite le_plus_minus_r.
 ring.
 apply mult_le_compat_r.
 apply fib_monotonic.
 replace (fib n * fib n) with (1 * (fib n * fib n)).
 rewrite mult_assoc_reverse.
 apply mult_le_compat; auto with arith.
 apply mult_le_compat_l.
 apply fib_monotonic.
 ring.
Qed.

Theorem fib_2n_plus_2 :
  forall n, fib (S (2*n+1)) = fib (n+1) * (fib (n+1)) + fib n * fib n.
Proof.
 intros n; replace (S (2*n+1)) with ((n+1)+(n+1)) by ring.
 rewrite fib_n_p'.
 replace (n + 1 + 1) with (S (S n)) by ring.
 rewrite fib_SSn.
 replace (S n) with (n + 1) by ring.
 rewrite (plus_comm (fib n) (fib (n + 1))).
 now rewrite minus_plus.
Qed.

Theorem th_fib_positive1 :
  forall p : positive,
  forall u v : nat,
    u = fib (nat_of_P p) /\ v = fib (S (nat_of_P p)) ->
      2*u*v - u*u = fib(nat_of_P (xI p)) /\
      v*v + u*u = fib(S (nat_of_P (xI p))).
Proof.
 intros p u v [Hu Hv]; rewrite Hu; rewrite Hv.
 rewrite nat_of_P_xI.
 replace (S (2* nat_of_P p)) with (2*nat_of_P p + 1) by ring.
 rewrite fib_2n_plus_1,  fib_2n_plus_2.
 replace (S (nat_of_P p)) with (nat_of_P p + 1) by ring; auto.
Qed.
          
Theorem th_fib_positive0 :
  forall p : positive,
  forall u v : nat,
    u = fib (nat_of_P p) /\ v = fib (S (nat_of_P p)) ->
    u*u + (v-u)*(v-u) = fib (nat_of_P (xO p)) /\
    2*u*v - u*u = fib (S (nat_of_P (xO p))).
Proof.
 intros p u v [Hu Hv]; subst.
 rewrite nat_of_P_xO.
 rewrite fib_2n.
 replace (S (nat_of_P p)) with (nat_of_P p + 1) by ring.
 replace (S (2*nat_of_P p)) with (2*nat_of_P p+1) by ring.
 rewrite fib_2n_plus_1; auto.
Qed.

Fixpoint fib_positive (p:positive) :
  {u:nat & { v : nat | u = fib (nat_of_P p) /\  v = fib (S (nat_of_P p))}} :=
match p return 
   {u:nat & { v : nat | u = fib (nat_of_P p) /\  v = fib (S (nat_of_P p))}}
     with
  xH => (existT (fun u=> { v : nat | u = 1 /\  v = 2})
              1 (exist (fun v => 1 = 1 /\  v = 2)
                    2 (conj (refl_equal 1) (refl_equal 2))))
| xI p' =>
   match fib_positive p' with
     (existT _ u (exist _ v h)) =>
       (existT (fun u =>
                  { v: nat | u = fib (nat_of_P (xI p')) /\
                             v = fib (S (nat_of_P (xI p')))})
           (2*u*v - u*u)
          (exist (fun w=> 2*u*v-u*u = fib (nat_of_P (xI p')) /\
                            w= fib (S (nat_of_P (xI p'))))
             (v*v + u*u) (th_fib_positive1 p' u v h)))
   end
| xO p' =>
   match fib_positive p' with
     (existT _ u (exist _ v h)) =>
       (existT (fun u =>
                  { v: nat | u = fib (nat_of_P (xO p')) /\
                             v = fib (S (nat_of_P (xO p')))})
            (u*u+(v-u)*(v-u))
          (exist (fun w => u*u+(v-u)*(v-u) = fib (nat_of_P (xO p'))/\
                           w = fib (S (nat_of_P (xO p'))))
                (2*u*v-u*u) (th_fib_positive0 p' u v h)))
   end
end.

Definition fib' :
  forall n:nat, {u : nat &{v : nat | u = fib n /\ v = fib (S n)}}.
Proof.
  intros n; case n.
 -  exists 1; exists 1; auto.
 -   intros n'; elim (fib_positive (P_of_succ_nat n'));
     intros u [v [Hu Hv]].
     exists u, v;
  rewrite Hu; rewrite Hv; rewrite nat_of_P_o_P_of_succ_nat_eq_succ; now split.
Qed.

(* Tests :
Recursive Extraction fib'.

*)
