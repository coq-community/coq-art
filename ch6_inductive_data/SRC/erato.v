
Require Import List.
Require Import Arith.

Fixpoint
  update_primes (k:nat) (l: list (nat*nat)) {struct l} : list (nat*nat)*bool :=
  match l with
  | nil => (nil,false)
  | (p,n)::tl => 
    let (l',b) := update_primes k tl in
    match Nat.compare  k n with
    | Lt => ((p, n)::l', b)
    | Eq => ((p, n+p)::l', true)
    | Gt => ((p, n+p)::l', b)
    end
  end.

Fixpoint prime_sieve (n:nat) : list (nat*nat) :=
  match n with
  | O => nil
  | 1 => nil
  | S k' => 
    let (l', b) := update_primes (S k')(prime_sieve k') in
    if b then l' else ((S k', 2*S k')::l')
  end.

Definition prime_fun (n:nat) : bool :=
  match prime_sieve n with
  | nil => false
  | (p,q)::tl => 
    match Nat.compare p n with
    | Eq => true
    | _ => false
    end
  end.

(** The rest of the file shows that we can prove interesting facts
   about our function using only the notions that have been introduced 
   in the book up to chapter 6.  However, an expert user would rather
   also rely on notions that are introduced later, like the inductive
   properties found in chapter 8. *)
 


Definition divides (p n:nat) := exists q:nat, n = p*q.

Definition prime (n:nat) :=
  (n<>0/\n<>1)/\~(exists k:nat, 1 < k < n /\ divides k n).

Definition all_list(P:nat->nat->Prop) (l:list(nat*nat)):=
 forall (l1 l2:list(nat*nat))(p n:nat),
   l = l1++(p, n)::l2 -> (P p n).

Definition all_first_less_than (k:nat) :=
 all_list (fun p n:nat => p < k).

Definition all_first_prime :=
 all_list (fun p n:nat => prime p).

Definition all_intervals (k:nat) :=
 all_list (fun p n:nat => n-p<k<=n).

Definition all_multiples :=
 all_list (fun p n:nat => exists q:nat, n=p*q).

Definition all_greater_than_one :=
 all_list (fun p n => 1 < p).

Definition all_prime_in_first (k:nat)(l:list (nat*nat)) :=
 forall n:nat, 0 < n < k -> prime n ->
  (exists l1: list (nat*nat),
    (exists l2: list (nat*nat),
      (exists p: nat, l= l1++(n,p)::l2))).

(** A theorem that should be in the general libraries. *)


Theorem mult_lt_reg_l : 
  forall m n p, m * n < m * p -> n < p.
Proof.
 intros m n; elim n.
 -  intros p; case p.
  +  repeat (rewrite mult_comm; simpl); auto.
  +  auto with arith.
 -  intros n' Hrec p; case p.
  +  rewrite <- (mult_comm 0); simpl; intros Hlt; elim (lt_n_O (m*S n'));auto.
  + intros p'; repeat rewrite <- mult_n_Sm.
    repeat rewrite <- (plus_comm m).
    intros Hlt; assert (Hlt' : m*n' < m* p').
    *  apply plus_lt_reg_l with m; auto.
    * auto with arith.
Qed.



(** A bunch of generic proofs about the all_list predicate. *)

Theorem all_list_transmit :
 forall (P:nat->nat->Prop)(p:nat*nat)(l:list(nat*nat)),
   all_list P (p::l)-> all_list P l.
Proof.
 intros P fst_elem l H l1 l2 p n Heq.
 unfold all_list in H.
 apply H with (fst_elem::l1) l2; rewrite Heq; auto.
Qed.

Theorem all_list_add :
 forall (P:nat->nat->Prop)(l:list(nat*nat))(p n:nat),
 P p n -> all_list P l -> all_list P ((p,n)::l).
Proof.
 intros P l p n Hp Hal l1; case l1.
 intros l2 p' n' Heq; injection Heq; intros Hl Hn' Hp';
 rewrite <- Hn'; rewrite <- Hp'; auto.

 simpl; clear l1; intros fst_elem l1 l2 p' n' Heq; injection Heq;
 intros Hl Hfst; apply (Hal l1 l2); assumption.
Qed.

Theorem absurd_decompose_list :
 forall (A:Set) (l1 l2:list A) (p:A), nil = l1++p::l2 -> False.
Proof.
 intros A l1; case l1; simpl; intros; discriminate.
Qed.

Theorem all_list_nil :
 forall (P:nat->nat->Prop),
  all_list P nil. 
Proof.
 intros P l1 l2 p n Heq; elim (absurd_decompose_list _ _ _ _ Heq).
Qed. 

(** As corollaries, we get transmission theorems for the main predicates. *)

Theorem all_intervals_transmit :
 forall (k:nat)(p:nat*nat)(l: list(nat*nat)),
  all_intervals k (p::l) -> all_intervals k l.
Proof.
 intros k; exact (all_list_transmit (fun p n => n-p<k<=n)).
Qed.

Theorem all_multiples_transmit :
 forall (p:nat*nat)(l: list(nat*nat)),
  all_multiples (p::l) -> all_multiples l.
Proof.
 exact (all_list_transmit (fun p n => exists q:nat, n=p*q)).
Qed.

Theorem all_greater_than_one_transmit :
 forall (p:nat*nat)(l: list(nat*nat)),
  all_greater_than_one (p::l) -> all_greater_than_one l.
Proof.
 exact (all_list_transmit (fun p n => 1<p)).
Qed.

Theorem all_first_prime_transmit :
 forall (p:nat*nat)(l:list(nat*nat)),
  all_first_prime(p::l) -> all_first_prime l.
Proof.
 exact (all_list_transmit (fun p n => prime p)).
Qed.

Theorem all_first_less_than_transmit :
 forall k (p:nat*nat)(l: list(nat*nat)),
  all_first_less_than k (p::l) -> all_first_less_than k l.
Proof.
 intros k; exact (all_list_transmit (fun p n => p < k)).
Qed.

(** Theorems about invariants in update_primes *)

Theorem update_primes_all_list_invariant :
 forall (P:nat->nat->nat->Prop),
 (forall k p n:nat, k = n -> P k p n -> P k p (n+p))->
 (forall k p n:nat, n < k -> P k p n -> P k p (n+p))->
 forall (k:nat)(l l':list(nat*nat))(b:bool),
  all_list (P k) l ->
  update_primes k l = (l',b) -> all_list (P k) l'.
Proof.
  intros P Hp2 Hp3 k l; elim l.
  -  simpl; intros Hal l' b Hup; injection Hup; intros Hb Hl';
       rewrite <- Hl'; apply (all_list_nil (P k)).
  -  simpl; intros (p, n) l0 Hrec l' b Hal;
       case_eq (update_primes k l0); intros l'0 b0 Hup0.
     case_eq (Nat.compare k n); intros Htwc Hup; injection Hup;
       intros Hb Hl'; rewrite <- Hl';
         generalize (Hal nil l0 p n (refl_equal _)); intros HPkpn;
           generalize (Hrec l'0 b0 (all_list_transmit (P k) (p,n) l0 Hal) Hup0);
           intros Hal'; apply all_list_add; auto.
     +  apply Hp2;[apply nat_compare_eq;auto| auto].
     + apply Hp3;[apply nat_compare_Gt_gt;auto| auto].
Qed.

(** Now a few proofs about divides and prime *)

Theorem divides_dec_aux : 
  forall k n p:nat, n <= k -> divides p n \/ ~divides p n.
Proof.
  intros k; elim k.
  -  intros n p Hle; left; exists 0; rewrite mult_comm; simpl; 
       symmetry; apply le_n_O_eq; auto.
  - intros k' Hrec n p Hlt; elim (le_lt_or_eq n (S k')).
    + auto with arith.
    + intros Heq; rewrite Heq.
      case p.
      *  right; intros (q, Heq').
         discriminate Heq'.
      *  intros p'; case_eq (Nat.compare (S p') (S k')); intros Htwc.
         --  assert (H:S p' = S k').
             { apply nat_compare_eq; auto. }
             left; exists 1; rewrite H.
             auto with arith.
         -- 
           assert (S p' < S k').
           apply nat_compare_Lt_lt; auto.
           elim (Hrec (minus (S k') (S p')) (S p')).
           ++ intros (q, Heq'); left; exists (S q).
              rewrite (le_plus_minus (S p') (S k')).
              ** rewrite Heq'.
                 repeat rewrite (mult_comm (S p')).
                 reflexivity.
              **  auto with arith.
           ++  intros Hndiv; right; intros Hdiv.
               apply Hndiv.
               elim Hdiv.
               intros q; case q.
               **  rewrite mult_comm;  simpl; intros; discriminate.
               **  intros q' Heq'; exists q'.
                   apply plus_reg_l with (S p').
                   rewrite le_plus_minus_r.
                   { rewrite Heq'.
                     rewrite plus_comm; rewrite mult_n_Sm; reflexivity.
                   }
                   auto with arith.
           ++ simpl; apply le_minus.
              
         -- assert (Hlt': S k' < S p').
            { apply nat_compare_Gt_gt; auto. }
            right; intros Hdiv; elim Hdiv; intros q; case q.
            ++  rewrite mult_comm; simpl; intros; discriminate.
            ++ intros q' Heq'; elim (lt_not_le _ _ Hlt').
               rewrite Heq'.
               rewrite mult_comm; simpl; auto with arith.
    +  trivial.
Qed.


Theorem eq_nat_or :
 forall n m:nat, n=m \/ ~n=m.
Proof.
  decide equality.
Qed.

Theorem prime_dec_aux :
 forall n k:nat,
  (n=0\/n=1)\/
  (exists p:nat, 1<p<k /\ (exists q:nat, n=p*q))\/
  ((n<>0/\n<>1)/\~(exists p:nat, 1<p<k/\ (exists q:nat, n=p*q))).
Proof.
 intros n; elim (eq_nat_or n 1).
 -  auto.
 - intros Hnneq1.
   elim (eq_nat_or n 0).
   +  auto.
   + intros Hnneq0 k; elim k.
    *  right; right; split.
     --   auto.
     -- intros (p, ((_,Hlt0), (q, Heq))).
        elim (lt_n_O p); auto.
    * intros k'; case k'.
     --  intros; right; right; split.
         ++ auto.
         ++ intros (p, ((Hpgt1, Hplt1),_)).
            elim (lt_irrefl 1); apply lt_trans with p;auto.
     -- intros k''; case k''.
        ++ intros; right; right; split; auto; intros (p, ((Hpgt1, Hplt2),_)).
           elim (lt_irrefl p); apply le_lt_trans with 1; auto with arith.
        ++ intros k''' Hrec; case (divides_dec_aux n n (S (S k'''))).
           ** auto with arith.
           ** intros Hdiv; right; left; exists (S (S k'''));
                repeat split; auto with arith.
           **  intros Hndiv; elim Hrec.
               { auto. }
               {  intros Hrec'; elim Hrec'.
                  intros (p, ((Hpgt1, Hplt), Hex));
                    right; left; exists p; repeat split;
                      auto with arith.
                  intros (_, Hnodiv); right; right; split; auto;
                    intros (p, ((Hpgt1, Hplt), Hex)).
                  assert (Hple : p <= S (S k''')).
                  { auto with arith. }
                  elim (le_lt_or_eq _ _ Hple).
                  intros Hplt'.
                  elim Hnodiv; exists p; repeat split; auto with arith.
                  intros Hpeq.
                  elim Hndiv; rewrite <- Hpeq; exact Hex.
               }
Qed.

Theorem prime_dec :
 forall n:nat, (n=0\/n=1)\/(exists p:nat, 1<p<n /\ (exists q:nat, n=p*q))\/
  prime n.
Proof.
 intros n; exact (prime_dec_aux n n).
Qed.


Theorem div_by_prime_aux :
 forall k:nat, forall n:nat, n <= k ->
 1 < n -> (exists p:nat, 1 < p < n /\ (exists q : nat, n=p*q)) ->
 (exists p:nat, 1 < p < n /\ (prime p) /\ (exists q:nat, n=p*q)).
Proof.
 intros k; elim k.
 -  intros n Hle Hlt Hn.
    elim (lt_asym 1 0). 
  +  apply lt_le_trans with n; assumption.
  + auto with arith.
 -  intros k' Hrec n Hle Hlt Hn.
    elim (le_lt_or_eq n (S k')).
    +  intros Hle'; apply Hrec; auto with arith.
    + elim Hn; intros p ((Hpgt1, Hpltn),(q,Heq)).
      intros HneqSk'.
      elim (prime_dec p).
    *  intros Hpeq0or1; elim Hpeq0or1.
     --  intros Hpeq0.
         rewrite Hpeq0 in Hpgt1; elim (lt_n_O 1); assumption.
     -- intros Hpeq1;
          rewrite Hpeq1 in Hpgt1; elim (lt_irrefl 1); assumption.
    *  intros Hpdec; elim Hpdec.
       -- intros Hexp.
          elim (Hrec p); auto with arith.
          ++ intros p' ((Hp'gt1,Hp'ltp), (Hpr,(q', Heq'))).
             exists p'.
             split;[split|split]; auto with arith.
             ** apply lt_trans with p; auto with arith.
             **  exists (q' * q).
                 rewrite mult_assoc.
                 rewrite Heq; rewrite Heq'; trivial.
          ++  unfold lt in Hpltn.
              rewrite HneqSk' in Hpltn; auto with arith.
       --  exists p;split;[split|split]; auto with arith.
           exists q; auto with arith.
    + trivial.
Qed.

Theorem div_by_prime :
 forall n:nat, 1 < n -> (exists p:nat, 1 < p < n /\ (exists q : nat, n=p*q)) ->
 (exists p:nat, 1 < p < n /\ (prime p) /\ (exists q:nat, n=p*q)).
Proof.
 intros n; apply (div_by_prime_aux n n).
 auto with arith.
Qed.

(** Now, theorems about update_primes. *)

Theorem update_primes_true_aux :
  forall (k:nat) (l1 l2 l3 l4: list(nat*nat))(b:bool),
    update_primes k l1 = (l2, true) ->
    update_primes k (l3++l1) = (l4, b) -> b=true.
Proof.
  intros k l1 l2 l3; elim l3.
  - simpl; intros l4 b Heq1; rewrite Heq1; intros Heq2; injection Heq2; auto.
  - simpl; intros (p,n) l; case (update_primes k (l++l1)).
    intros l4 b Hrec l4' b'; case (Nat.compare k n).
  + intros Heq1 Heq2; injection Heq2; auto.
  +  intros Heq1 Heq2; injection Heq2.
     intros Heq3 Heq4; rewrite <- Heq3; apply Hrec with l4; auto.
  + intros Heq1 Heq2; injection Heq2.
    intros Heq3 Heq4; rewrite <- Heq3; apply Hrec with l4; auto.
Qed.

Theorem update_primes_true_imp_div :
  forall (k:nat)(l: list (nat*nat)),
    all_first_less_than k l ->
    all_multiples l ->
    all_greater_than_one l ->
    forall l1, update_primes k l = (l1, true) ->
               (exists p:nat, 1< p < k /\ (exists q:nat, k = p*q)).
Proof.
  intros k l; elim l.
  -  simpl; intros; discriminate.
  - intros (p,n) l0 Hrec Haf Ham Hal l1; simpl.
    case_eq (update_primes k l0).
    intros l2 b Hup; case_eq (Nat.compare k n).
    +  intros Htwc Heq; generalize (nat_compare_eq _ _ Htwc).
       intros Hk; exists p; split.
       *  split.
          unfold all_greater_than_one in Hal;
            apply Hal with (nil (A:=nat*nat)) l0 n; auto.
          unfold all_first_less_than in Haf;
            apply Haf with (nil (A:=nat*nat)) l0 n; auto.
       * unfold all_multiples in Ham.
         rewrite Hk; apply Ham with (nil (A:=nat*nat)) l0; auto.
    + intros Htwc Heq; injection Heq; intros Hb Hl1.
      * rewrite Hb in Hup; apply Hrec with l2.
        -- apply all_first_less_than_transmit with (p,n); auto.
        -- apply all_multiples_transmit with (p,n); auto.
        --  apply all_greater_than_one_transmit with (p,n); auto.
        -- auto.
           
    + intros Htwc Heq; injection Heq; intros Hb Hl1.
      rewrite Hb in Hup; apply Hrec with l2.
      * apply all_first_less_than_transmit with (p,n); auto.
      * apply all_multiples_transmit with (p,n); auto.
      *  apply all_greater_than_one_transmit with (p,n); auto.
      *  auto.
Qed.

Theorem interval_eq :
  forall p q q', p*q'-p < p*q <= p*q' -> q=q'.
Proof.
  intros p; case p.
  -  simpl; intros q q' (Hlt, Hle); elim (lt_irrefl 0);assumption.
  - intros p' q q' (Hlt, Hle).
    apply le_antisym.
    + apply mult_S_le_reg_l with p'; auto.
    + assert (Hlt' : (q' - 1)*S p' < S p' * q).
     { rewrite mult_minus_distr_r.
       rewrite mult_1_l.
       rewrite (mult_comm q').
       assumption.
     }
     rewrite (mult_comm (q' - 1)) in Hlt'.
     generalize (mult_lt_reg_l _ _ _ Hlt').
     case q'; simpl.
     * auto with arith.
       * intros n; rewrite <- minus_n_O; auto with arith.
Qed.


Theorem update_primes_false_imp_prime :
 forall k l l1,
   1 < k ->
   all_multiples l ->
   all_intervals k l ->
   all_prime_in_first k l ->
   update_primes k l = (l1,false) -> prime k.
Proof.
 intros k l l1 Hkgt1 Ham Hai Hap Heq.
 elim (prime_dec k); auto.
 -  intros Hkeq0or1;elim Hkeq0or1.
    + intros Hkeq0.
      rewrite Hkeq0 in Hkgt1; elim (lt_n_O 1); assumption.
    + intros Hkeq1; rewrite Hkeq1 in Hkgt1; elim (lt_irrefl 1); assumption.
- intros Hpdec; elim Hpdec.
  + intros Hexdiv.
    generalize (div_by_prime _ Hkgt1 Hexdiv).
    intros (p, ((Hpgt1,Hpltk), (Hpr, Hex))).
    elim (Hap p); auto.
    *  intros l'1 (l2, (n, Heq')).
       elim Hex; intros q Heq''. 
       assert (Hint: n - p < k <= n).
     { unfold all_intervals in Hai.
       apply Hai with l'1 l2. 
       auto.
     }
     assert (Hmult : (exists q':nat, n = p*q')).
     {
       unfold all_multiples in Ham.
       apply Ham with l'1 l2.
       auto.
     }
     elim Hmult; intros q' Heq3.
     assert (Heq4: q=q').
     {
       apply interval_eq with p.
       rewrite <- Heq3.
       rewrite <- Heq''.
       assumption.
     }
     assert (false= true).
     { 
       case_eq (update_primes k ((p,n)::l2)).
       intros l3 b Hup.
       generalize (update_primes_true_aux k ((p,n)::l2) l3 l'1 l1 false).
       intros H; apply H.
       - generalize Hup.
         simpl.
         case (update_primes k l2).
         intros l5 b2.
         rewrite Heq''; rewrite Heq3; rewrite Heq4.
         rewrite Nat.compare_refl.
         intros Heq5; injection Heq5; intros Heq6 Heq7;
           rewrite Heq6;rewrite Heq7;
             auto with arith.
       -  rewrite <- Heq'.
          assumption.
     }  
     discriminate.
    * auto with arith.
  + trivial.
Qed.

(** We can now prove that all properties are invariant. *)

Theorem update_primes_all_multiples :
  forall k l l' b,
    all_multiples l ->
       update_primes k l = (l', b) -> all_multiples l'.
Proof.
 apply (update_primes_all_list_invariant (fun k p n => exists q:nat, n=p*q));
 try (intros k p n Hcomp (q, Heq);exists (S q);rewrite Heq;
 rewrite <- mult_n_Sm; reflexivity).
Qed.


Theorem update_primes_all_first_less_than :
 forall k l l' b,
 all_first_less_than k l ->
 update_primes k l = (l',b) ->
 all_first_less_than k l'.
Proof.
 apply (update_primes_all_list_invariant (fun k p n => p < k)); auto.
Qed.


Theorem update_primes_all_greater_than_one :
 forall k l l' b,
  all_greater_than_one l ->
  update_primes k l = (l',b) ->
  all_greater_than_one l'.
Proof.
 apply (update_primes_all_list_invariant (fun k p n => 1 < p)); auto.
Qed.

Theorem update_primes_all_first_prime :
 forall k l l' b,
  all_first_prime l -> update_primes k l = (l',b) -> all_first_prime l'.
Proof.
 apply (update_primes_all_list_invariant (fun k p n => prime p)); auto.
Qed.

Theorem update_primes_all_intervals :
 forall (k:nat)(l:list(nat*nat)),
   all_intervals k l -> all_greater_than_one l ->
   forall l' b, update_primes k l = (l',b) -> all_intervals (S k) l'.
Proof.
 intros k l; elim l.
 -  simpl; intros Hai Hal l' b Hup; injection Hup;
      intros Hb Hl'; rewrite <- Hl'.
    intros l1 l2 n p Heq; elim (absurd_decompose_list _ _ _ _ Heq).
 -  simpl; intros (p, n) l0 Hrec Hai Hal l' b;
      case_eq (update_primes k l0); intros l'0 b0 Hup0 Hup l1.
    case l1.
    + unfold all_intervals in Hai.
      case_eq (Nat.compare k n); simpl; intros Htwc l2 p' n' Heq;
        rewrite Htwc in Hup; injection Hup; intros Hb Hl';
          rewrite <- Hl' in Heq; injection Heq; intros Hl2 Hn' Hp';
            rewrite <- Hp'; rewrite <- Hn';
              generalize (Hai nil l0 p n (refl_equal _));
              intros (Hlt, Hle);split; 
                (generalize (nat_compare_Lt_lt _ _ Htwc) ||
                 generalize (nat_compare_eq _ _ Htwc) ||
                 generalize (nat_compare_Gt_gt _ _ Htwc));
                auto with arith. (* ICI *)
      *  intros Heq2; rewrite Heq2; rewrite plus_comm; rewrite minus_plus;
           auto with arith.
      * intros Heq2; rewrite Heq2; unfold all_greater_than_one in Hal;
          generalize (Hal nil l0 p n (refl_equal _)); intros Hpgt1.
        pattern n at 1; rewrite plus_n_O; rewrite plus_n_Sm;
          apply plus_le_compat; auto with arith.
      * rewrite plus_comm; rewrite minus_plus; auto with arith.
      *  generalize (Hal nil l0 p n (refl_equal _)); intros Hpgt1.
         intros Hkltn; pattern k at 1; rewrite plus_n_O; rewrite plus_n_Sm;
           apply plus_le_compat; auto with arith.
    + generalize (all_intervals_transmit _ _ _ Hai); intros Hai'.
      generalize (all_greater_than_one_transmit _ _ Hal); intros Hal'.
      simpl; clear l1; intros fst_elem l1 l2 p' n' Heq; generalize Hup;
        rewrite Heq.
      case (Nat.compare k n); intros Hup'; injection Hup'; 
        intros Hb Hl' _; apply (Hrec Hai' Hal' l'0 b0 Hup0 l1 l2); assumption.
Qed.

Theorem all_first_less_than_S :
  forall k l, all_first_less_than k l -> all_first_less_than (S k) l.
Proof.
  intros k l; elim l.
  -  intros Haf l1 l2 p n Heq; elim (absurd_decompose_list _ _ _ _ Heq).
  -  intros (p,n) l0 Hrec Haf l1.
     case l1.
     +  intros l2 p' n' Heq;
          generalize (Haf nil l2 p' n' Heq); intros Hpltk.
        auto with arith.
     + simpl; clear l1; intros fst_elem l1 l2 p' n' Heq.
       injection Heq; intros; 
         apply (Hrec (all_first_less_than_transmit _ _ _ Haf) l1 l2 p' n');
         assumption.
Qed.

Theorem all_intervals_add :
 forall (l:list(nat*nat))(k p n:nat),
  n-p < k <= n ->
  all_intervals k l ->
  all_intervals k ((p,n)::l).
Proof.
 intros l k p n Hint Hai l1; case l1.
 - intros l2 p' n' Heq; injection Heq; intros Hl Hn' Hp';
     rewrite <- Hn'; rewrite <- Hp'; auto.
 -  simpl; clear l1; intros fst_elem l1 l2 p' n' Heq; injection Heq;
      intros Hl Hfst; apply (Hai l1 l2); assumption.
Qed.

Theorem all_first_prime_add :
  forall (l:list(nat*nat))(p n:nat),
    prime p ->
    all_first_prime l -> all_first_prime ((p,n)::l).
Proof.
  intros l p n Hlt Haf l1; case l1.
  -  intros l2 p' n' Heq; injection Heq; intros Hl Hn' Hp';
       rewrite <- Hp'; assumption.
  -  simpl; clear l1; intros fst_elem l1 l2 p' n' Heq; injection Heq;
       intros Hl Hfst; apply (Haf l1 l2 p' n' Hl).
Qed.

Theorem all_multiples_add :
  forall l n p,
    (exists q:nat, n=p*q)->
    all_multiples l ->
    all_multiples ((p,n)::l).
Proof.
  intros l n p Hdiv Ham l1; case l1.
  - simpl; intros l2 p' n' Heq; injection Heq;
      intros Hl2 Hn' Hp'; rewrite <- Hn'; rewrite <- Hp';
        assumption.

  - clear l1; simpl; intros fst_elem l1 l2 p' n' Heq; injection Heq;
      intros Hl Hfst; apply (Ham l1 l2); assumption.
Qed.

Theorem all_greater_than_one_add :
  forall l n p,
    1 < p -> all_greater_than_one l ->
    all_greater_than_one ((p,n)::l).
Proof.
  intros l n p Hlt Hal  l1; case l1.
  - simpl; intros l2 p' n' Heq; injection Heq;
      intros Hl2 Hn' Hp'; rewrite <- Hp';
        assumption.
  -  clear l1; simpl; intros fst_elem l1 l2 p' n' Heq; injection Heq;
       intros Hl Hfst; apply (Hal l1 l2 p' n'); assumption.
Qed.

Fixpoint same_first (l1 l2:list(nat*nat)) {struct l1} : bool :=
  match l1, l2 with
    nil, nil => true
  | ((a, _)::l'1), ((b, _)::l'2) =>
    match Nat.compare a b with
    | Eq => same_first l'1 l'2
    | _ => false
    end
  | _, _ => false
  end.

Theorem update_primes_same_first :
  forall k l l' b,
    update_primes k l = (l', b) ->
    forall l1 l2 p n,
      l = l1++(p,n)::l2 -> 
      (exists l'1 : list(nat*nat),
          (exists l'2 : list(nat*nat),
              (exists n': nat,
                  l'=l'1++(p,n')::l'2))).
Proof.
  intros k l; elim l.
  - intros l' b Hup l1 l2 p n Heq; elim (absurd_decompose_list _ _ _ _ Heq).

  - intros (p,n) l0 Hrec l' b.
    simpl; case_eq (update_primes k l0); intros l'0 b0 Hup'.
    case (Nat.compare k n); intros Hup; injection Hup;
      intros Hb Hl'; intros l1; (case l1; [simpl; intros l2 p0 n0 Heq;
                                           injection Heq; intros Hl2 Hn0 Hp0; rewrite <- Hl'; rewrite <- Hp0;
                                           exists (nil (A:=nat*nat)); exists l'0 | 
                                           clear l1; simpl; intros fst_elem l1 l2 p0 n0 Heq; injection Heq;
                                           intros Hl0 Hfst_elem; rewrite <- Hl';
                                           elim (Hrec l'0 b0 Hup' l1 l2 p0 n0 Hl0); intros l'1 (l'2, (n', Heq2));
                                           rewrite Heq2]).
    +  exists (n+p); reflexivity.
    +  exists ((p,n+p)::l'1); exists l'2; exists n'; reflexivity.
    + exists n; reflexivity.
    +  exists ((p,n)::l'1); exists l'2; exists n'; reflexivity.
    +  exists (n+p); reflexivity.
    + exists ((p,n+p)::l'1); exists l'2; exists n'; reflexivity.
Qed.

Theorem update_primes_all_prime_in_first :
 forall k l l' b,
  all_prime_in_first k l ->
  update_primes k l = (l', b) ->
  all_prime_in_first k l'.
Proof.
 intros k l l' b Hap Hup p Hplek Hpr.
 elim (Hap p Hplek Hpr); intros l'1 (l'2, (n', Heq)).
 apply (update_primes_same_first k l l' b Hup l'1 l'2 p n' Heq).
Qed.


Theorem prime_sieve_invariant :
  forall k l,
    prime_sieve (S k)=l ->
    all_first_less_than (S (S k)) l /\
    all_first_prime l /\
    all_prime_in_first (S (S k)) l /\
    all_intervals (S (S k)) l /\
    all_multiples l /\
    all_greater_than_one l.
Proof.
  intros k; elim k.
  -   simpl; intros l Hl; rewrite <- Hl; clear Hl l.
      split;[idtac | split; [idtac | split;[idtac|split;[idtac|split]]]];
        try (intros l1 l2 p n Heq; elim (absurd_decompose_list _ _ _ _ Heq)).
      intros n Hle1 ((Hnneq0, Hnneq1),_); elim Hnneq1.
      elim Hle1; intros; apply (le_antisym n 1); auto with arith.
  - 
    intros k' Hrec l Hps.
    change ((let (l', b) := 
                 update_primes (S (S k')) (prime_sieve (S k')) in
             if b then l' else (S (S k'), 2*S (S k'))::l') = l) in Hps.
    case_eq (update_primes (S (S k')) (prime_sieve (S k'))); intros l' b Heq.
    generalize (Hrec (prime_sieve (S k'))); intros Hrec'.
    assert (Hal: all_first_less_than (S (S k')) l').
    {
      apply update_primes_all_first_less_than with (prime_sieve (S k')) b; auto.
      intuition.
    }
    assert (Hafp: all_first_prime l').
    { apply update_primes_all_first_prime 
        with (S (S k')) (prime_sieve (S k')) b; auto.
      intuition.
    }
    assert (Hapf: all_prime_in_first (S (S k')) l').
    { apply update_primes_all_prime_in_first with (prime_sieve (S k')) b; auto.
      intuition.
    }
    assert (Hai : all_intervals (S (S (S k'))) l').
    {
      apply update_primes_all_intervals with (prime_sieve (S k')) b; auto.
      intuition.
      intuition.
    }

    assert (Ham : all_multiples l').
    { apply update_primes_all_multiples 
        with (S (S k')) (prime_sieve (S k')) b; auto.
      intuition.
    }
    assert (Ha1 : all_greater_than_one l').
    {
      apply update_primes_all_greater_than_one with (S (S k')) (prime_sieve (S k')) b; auto.
      intuition.
    }
    case_eq b; intros Heqb; rewrite Heqb in Heq; rewrite Heq in Hps.
    + rewrite <- Hps.
      split;[idtac|split;[idtac|split;[idtac|split;[idtac|split;[idtac|idtac]]]]]; 
        auto.
      * apply all_first_less_than_S; assumption.
      * unfold all_prime_in_first.
        intros n Hint Hpr; unfold all_prime_in_first in Hapf; apply Hapf; auto.
        split.
        -- intuition.
        -- elim Hint.
           intros Hngt0 Hnlek.
           elim (le_lt_or_eq _ _ Hnlek).
           ++ auto with arith; fail.
           ++ intros Hn'; injection Hn'.
              intros Hn; rewrite Hn in Hpr; elim Hpr.
              intros _ Hnex; elim Hnex.
              unfold divides.
              apply update_primes_true_imp_div with (prime_sieve (S k')) l'.
              ** intuition.
              ** intuition.
              ** intuition.
              ** auto.
    + split.
      * 
        intros l1; case l1.
        -- simpl; intros l2 p n; rewrite <- Hps; intros Heq2;injection Heq2.
           intros Hl2 Hn Hp; rewrite <- Hp; auto with arith.
        -- intros fst_elem l'1 l2 p n; simpl; rewrite <- Hps; intros Heq2;
             injection Heq2; intros Hl' Hfst_elem.
           assert (Hal' : all_first_less_than (S (S (S k'))) l').
           { apply all_first_less_than_S; auto. }
           apply (Hal' l'1 l2 p n); auto.
      * split.
        -- rewrite <- Hps; apply all_first_prime_add; auto.
           apply update_primes_false_imp_prime with (prime_sieve (S k')) l';
             try tauto.
           auto with arith.
        -- split.
           ++ rewrite <- Hps.
              intros n (Hpos, Hle) Hpr.
              elim (le_lt_or_eq _ _ Hle).
              ** intros Hlt; elim (Hapf n); auto with arith.
                 intros l'1 (l'2, (p, Heq2));
                   exists ((S (S k'), 2*S(S k'))::l'1); exists l'2; exists p.
                 rewrite Heq2;reflexivity.
              ** intros Hn'; injection Hn'; intros Hn.
                 exists (nil (A:=nat*nat)); exists l'; exists (2*S (S k')).
                 rewrite Hn;reflexivity.
           ++ split.
              ** rewrite <- Hps; apply all_intervals_add; auto with arith.
                 split.
                 { simpl.
                   rewrite minus_plus.
                   rewrite <- plus_n_O.
                   auto with arith.
                 }
                 { simpl.
                   repeat rewrite <- plus_n_Sm.
                   auto with arith.
                 }

              ** split.
                 { rewrite <- Hps; apply all_multiples_add; auto with arith. 
                   exists 2; rewrite (mult_comm 2); reflexivity. }

                 rewrite <- Hps.
                 apply all_greater_than_one_add; auto with arith.
Qed.

Theorem prime_fun_sound :
  forall k, prime_fun k = true -> prime k.
Proof.
  intros k0; case k0.
  - simpl; intros; discriminate.
  -  intros k; unfold prime_fun.
     case_eq (prime_sieve (S k)).
     +  
       intros; discriminate.
     + intros (p,n) l Heq; case_eq (Nat.compare p (S k));
         try(intros; discriminate; fail).
       intros Htwc _.
       assert (Hap:all_first_prime ((p,n)::l)).
       {  generalize (prime_sieve_invariant k ((p,n)::l) Heq); intuition. }
       rewrite <- (nat_compare_eq _ _ Htwc).
       apply (Hap nil l p n); auto.
Qed.

Theorem prime_fun_complete :
  forall k, prime k -> prime_fun k = true.
Proof.
  intros k; case k.
  -  intros ((Hneq0, Hneq1),Hnex); elim Hneq0; auto.
  - intros k'; case k'.
    +  intros ((Hneq0, Hneq1),Hnex); elim Hneq1; auto.
    + intros k'' ((_,_),Hnex); unfold prime_fun.
      assert (Hps: prime_sieve (S (S k'')) = 
                   let (l',b) := (update_primes (S (S k'')) (prime_sieve (S k''))) 
                   in
                   if b then l' else ((S (S k''), 2*S (S k''))::l')).
      {  auto. }
      rewrite Hps.
      case_eq  (update_primes (S (S k'')) (prime_sieve (S k''))).
      intros l' b; case b; intros Hup.
      *  elim Hnex.
         unfold divides.
         generalize (prime_sieve_invariant k'' (prime_sieve (S k'')));
           intros Hinv.
         apply (update_primes_true_imp_div (S (S k''))
                                           (prime_sieve (S k''))) with l';
           intuition.
      *  rewrite (Nat.compare_refl (S (S k''))); auto.
Qed.
