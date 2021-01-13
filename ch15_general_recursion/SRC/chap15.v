Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export Omega.
Require Export Zwf.
Require Export Relations.
Require Export Inverse_Image.
Require Export Transitive_Closure.

(** Euclidean division with bounded recursion (argument "b")
*)

Fixpoint bdiv_aux (b m n:nat){struct b} : nat*nat :=
  match b with
  | O => (0, 0)
  | S b' =>
      match le_gt_dec n m with
      | left H =>
          match bdiv_aux b' (m-n) n with
          | pair q r => (S q, r)
          end
      | right H => (0, m)
      end
  end.


Theorem bdiv_aux_correct1 :
 forall b m n:nat, m <= b -> 0 < n -> 
 m = fst (bdiv_aux b m n) * n + snd (bdiv_aux b m n).
Proof.
 intros b; elim b; simpl.
 -  intros m n Hle; inversion Hle; auto.
 -  intros b' Hrec m n Hleb Hlt; case (le_gt_dec n m); simpl; auto.
    intros Hle; generalize (Hrec (m-n) n);
    case (bdiv_aux b' (m-n) n); simpl; intros q r Hrec'.
    rewrite <- plus_assoc; rewrite <- Hrec'; auto with arith.
    omega. 
Qed.

Lemma  bdiv_aux_correct2 :
 forall b m n:nat, m <= b -> 0 < n -> snd (bdiv_aux b m n) < n.
Proof.
 intros b; elim b; simpl;auto.
 intros b' Hrec m n Hleb Hlt; case (le_gt_dec n m); simpl; auto.
 intros Hle; generalize (Hrec (m-n) n);
 case (bdiv_aux b' (m-n) n); simpl; intros q r Hrec'.
 apply Hrec'; [omega | auto].
Qed.


Definition bdiv :
  forall m n:nat, 0 < n -> {q:nat & {r:nat | m = q * n + r /\ r < n}}.
Proof.
  refine
  (fun (m n:nat)(h:0 < n) =>
    let p := bdiv_aux m m n in
    existT (fun q:nat => {r : nat | m = q*n+r /\ r < n})
      (fst p)(exist _ (snd p) _)).
  unfold p; split.
  - apply bdiv_aux_correct1; auto.
  -  eapply bdiv_aux_correct2; eauto.
Defined.

(** Tests :

Time Eval lazy beta iota zeta delta in (bdiv_aux 2000 2000 31).

Time Eval lazy beta delta iota zeta in
  match bdiv 2000 31 (lt_O_Sn 30) with
    existT _ q (exist _ r h) => (q,r)
  end.

*)

Require Import Lt.

(** Also proven in Coq.Arith.Wf_nat *)

Theorem lt_Acc : forall n:nat, Acc lt n.
Proof.
 induction n.
 - split; intros p H; inversion H.
 -  split; intros y H0.
    inversion H0.
    + assumption.     
    + destruct IHn; auto. 
Qed.

Theorem lt_wf : well_founded lt.
Proof.  exact lt_Acc. Qed.


(** This example illustrates that the relation associated with
   an inductive type : "t is an immediate subterm of t' " is well-founded.
  
   Our example uses the "positive" datatype, whith the unary constructors
   xO and xI, but the same technique works with Peano numbers, lists,
   binary trees, etc. *)
   

Inductive Rpos_div2 : positive->positive->Prop :=
  Rpos1 : forall x:positive, Rpos_div2 x (xO x)
| Rpos2 : forall x:positive, Rpos_div2 x (xI x).

Theorem Rpos_div2_wf : well_founded Rpos_div2.
Proof.
 unfold well_founded; intros a; elim a;
  (intros; apply Acc_intro; intros y Hr; inversion Hr; auto).
Qed.


(** Euclidean division with well-founded recursion *)

(** Specification of euclidean division *)

Definition div_type (m:nat) :=
  forall n:nat, 0 < n -> {q:nat &{r:nat | m = q*n+r /\ r < n}}.

(** Some derived types, useful for building div_F *)

Definition div_type' (m n q:nat) :=
  {r:nat | m = q*n+r /\ r < n}.

Definition div_type'' (m n q r:nat) := m = q*n+r /\ r < n.

(** Functional associated with the recursive computation process *)

Definition div_F :
  forall x:nat, (forall y:nat, y < x -> div_type y) -> div_type x.
Proof.
 unfold div_type at 2.
 refine
  (fun m div_rec n Hlt =>
     match le_gt_dec n m with
     | left H_n_le_m =>
         match div_rec (m-n) _ n _ with
         | existT _ q (exist _ r H_spec) =>
             existT (div_type' m n)(S q)
               (exist (div_type'' m n (S q)) r _)
         end
     | right H_n_gt_m =>
         existT (div_type' m n) 0
            (exist (div_type'' m n 0) m _)
     end); unfold div_type''; auto with arith.
  elim H_spec; intros H1 H2; split; auto.
  rewrite (le_plus_minus n m H_n_le_m); rewrite H1; ring.
Qed.

Definition div :
  forall m n:nat, 0 < n -> {q:nat &{r:nat | m = q*n+r /\ r < n}} :=
  well_founded_induction lt_wf div_type div_F.

Require Import chap9. (* For properties of div2 *)
Open Scope nat_scope.

Lemma f_lemma :
  forall x v:nat, v <= div2 x -> div2 x + v <= x.
Proof.
  intros x v H; generalize (double_div2_le x);  omega.
Qed.

#[export] Hint Resolve div2_le f_lemma double_div2_le : core.

Definition nested_F :
  forall x:nat, (forall y:nat, y < x -> {v:nat | v <= y}) -> {v:nat | v <= x }.
Proof.
refine
  (fun x => match x return (forall y:nat, y < x ->{v:nat | v <= y})->
                          {v:nat | v <= x} with
              O => fun f => exist _ 0 _
            | S x' => 
              fun f => match f (div2 x') _ with
                        exist _ v H1 =>
                        match f (div2 x' + v) _ with
                          exist _ v1 H2 => exist _ (S v1) _
                        end
                      end
            end); auto with arith.
  apply le_n_S;  eauto with arith.
Defined.

Definition nested_f :=
  well_founded_induction
    lt_wf (fun x:nat => {v:nat | v <= x}) nested_F.


Definition div_it_F (f:nat->nat->nat*nat)(m n:nat) :=
  match le_gt_dec n m with
  | left _ => let (q, r) := f (m-n) n in (S q, r)
  | right _ => (0, m)
  end.

Fixpoint iter {A:Type}(n:nat)(F:A->A)(g:A){struct n} : A :=
  match n with O => g | S p => F (iter  p F g) end.

Definition div_it_terminates :
  forall n m:nat, 0 < m ->
    {v:nat*nat |
     exists p:nat,
      (forall k:nat, p < k -> forall g:nat->nat->nat*nat,
           iter k div_it_F g n m = v)}.
Proof.
  intros n; elim n using (well_founded_induction lt_wf).
  intros n' Hrec m Hlt.
  case_eq (le_gt_dec m n'); intros H Heq_test.
  -  case Hrec with (y := n'-m)(2 := Hlt); auto with arith.
     intros [q r]; intros Hex; exists (S q, r).
     elim Hex; intros p Heq.
     exists (S p).
     intros k.
     case k.
     +  intros; elim (lt_n_O (S p)); auto.
     +  intros k' Hplt g; simpl; unfold div_it_F at 1.
        rewrite Heq; auto with arith.
        rewrite Heq_test; auto.
  -  exists (0, n'); exists 0; intros k; case k.
     + intros; elim (lt_irrefl 0); auto.
     +  intros k' Hltp g; simpl; unfold div_it_F at 1.
        rewrite Heq_test; auto.
Defined.

Definition div_it (n m:nat)(H:0 < m) : nat*nat :=
  let (v, _) := div_it_terminates n m H in v.


Definition max (m n:nat) : nat :=
  match le_gt_dec m n with left _ => n | right _ => m end.

Theorem max1_correct : forall n m:nat, n <= max n m.
 intros n m; unfold max; case (le_gt_dec n m); auto with arith.
Qed.

Theorem max2_correct : forall n m:nat, m <= max n m.
 intros n m; unfold max; case (le_gt_dec n m); auto with arith.
Qed.

#[export] Hint Resolve max1_correct max2_correct : arith.

Theorem div_it_fix_eqn :
 forall (n m:nat)(h:(0 < m)),
   div_it n m h =
   match le_gt_dec m n with
   | left H => let (q,r) := div_it (n-m) m h in (S q, r)
   | right H => (0, n)
   end.
Proof.
 intros n m h; unfold div_it; case (div_it_terminates n m h).
 intros v Hex1; case (div_it_terminates (n-m) m h).
 intros v' Hex2; elim Hex2; elim Hex1; intros p Heq1 p' Heq2.
 rewrite <- Heq1 with
     (k := S (S (max p p')))(g := fun x y:nat => v).
 -  rewrite <- Heq2 with (k := S (max p p'))(g := fun x y:nat => v).
    reflexivity.
    eauto with arith.
 -  eauto with arith.
Qed.

Theorem div_it_correct1 :
 forall (m n:nat)(h:0 < n),
   m = fst (div_it m n h) * n + snd (div_it m n h).
Proof.
 intros m; elim m using (well_founded_ind lt_wf).
 intros m' Hrec n h; rewrite div_it_fix_eqn.
 case (le_gt_dec n m'); intros H; trivial.
 pattern m' at 1; rewrite (le_plus_minus n m'); auto.
 pattern (m'-n) at 1.
 rewrite Hrec with (m'-n) n h; auto with arith.
 case (div_it (m'-n) n h); simpl; auto with arith.
Qed.

(** Recursion on an Ad-hoc Predicate 
*)

Inductive log_domain : nat->Prop :=
  log_domain_1 : log_domain 1
| log_domain_2 :
    forall p:nat, log_domain (S (div2 p))-> log_domain (S (S p)).


Theorem log_domain_non_O : forall x:nat, log_domain x -> x <> 0.
Proof.
 intros x H; case H; intros; discriminate.
Qed.

Theorem log_domain_inv :
 forall x p:nat, log_domain x -> x = S (S p)-> log_domain (S (div2 p)).
Proof.
 intros x p H; case H; try (intros H'; discriminate H').
 intros p' H1 H2; injection H2; intros H3; 
 rewrite <- H3; assumption.
Defined.

Fixpoint log (x:nat)(h:log_domain x){struct h} : nat :=
  match x as y return x = y -> nat with
  | 0 => fun h' => False_rec nat (log_domain_non_O x h h')
  | S 0 => fun h' => 0
  | S (S p) => 
       fun h' => S (log (S (div2 p))(log_domain_inv x p h h'))
  end (refl_equal x).


(** Another definition of the logarithm, using division by 2 
*)

Inductive log2_domain : nat->Prop :=
  l21 : log2_domain 1
| l22 : forall x:nat,
        x <> 1 -> x <> 0 -> log2_domain (div2 x) -> log2_domain x.

Lemma log2_domain_non_zero : forall x:nat, log2_domain x -> x <> 0.
Proof.
 induction 1.
 -  discriminate.
 - generalize (div2_le x); intro;omega.
Qed.

Theorem log2_domain_invert :
 forall x:nat, log2_domain x -> x <> 0 -> x <> 1 -> log2_domain (div2 x).
Proof.
 intros x h; case h.
 - intros h1 h2; elim h2; reflexivity.
 - intros; assumption.
Defined. 

Fixpoint log2 (x:nat)(h:log2_domain x){struct h} : nat :=
  match eq_nat_dec x 0 with
  | left heq => False_rec nat (log2_domain_non_zero x h heq)
  | right hneq =>
      match eq_nat_dec x 1 with
      | left heq1 => 0
      | right hneq1 =>
          S (log2 (div2 x)(log2_domain_invert x h hneq hneq1))
      end
  end.

Scheme log_domain_ind2 := Induction for log_domain Sort Prop.

Fixpoint two_power (n:nat) : nat :=
  match n with
  | O => 1
  | S p => 2 * two_power p
  end.

Section proof_on_log.
  
Theorem pow_log_le :
 forall (x:nat)(h:log_domain x), two_power (log x h) <= x.
Proof.
 intros x h; elim h using log_domain_ind2.
 simpl; auto with arith.
 intros p l Hle.
 lazy beta iota zeta delta [two_power log_domain_inv log];
  fold log two_power.
 apply le_trans with (2 * S (div2 p)); auto with arith.
 generalize (double_div2_le (S (S p))); simpl;intro;omega.
Qed.

End proof_on_log.


