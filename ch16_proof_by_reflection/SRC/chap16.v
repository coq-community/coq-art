Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export Omega.
Require Export Zwf.
Require Export Relations.
Require Export Inverse_Image.
Require Export Transitive_Closure.
Require Export Zdiv.

Open Scope nat_scope.

Theorem verif_divide :
    forall m p:nat, 0 < m -> 0 < p ->
    (exists q:nat, m = q*p)->(Z_of_nat m mod Z_of_nat p = 0)%Z.
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
       elim (lt_irrefl 0);exact Hlt.
    +  intros q' Heq; rewrite Heq.
       rewrite mult_comm; simpl; auto with arith.
Qed.

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

(** Tests :

Compute check_primality 2333.

Compute check_primality 2330.
*)


Fixpoint check_range' (v:Z)(r:nat){struct r} : bool :=
  match r with
    0 => true | 1 => true
  | S r' =>
      match (v mod Z_of_nat r)%Z with
      | 0%Z => false
      | _ => check_range' v r'
      end
  end.

Definition check_primality' (n:nat) :=
  check_range' (Zpos (P_of_succ_nat (pred n)))(pred (pred n)).

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
 -  auto.
 -  intros p Hd; elim p.
    +  unfold Z.abs_nat; intros p' Hrec; rewrite nat_of_P_xI.
       rewrite inj_S.
       rewrite inj_mult.
       rewrite Zpos_xI.
       unfold Z.succ.
       rewrite Hrec.
       simpl; auto.
    +  unfold Z.abs_nat.
       intros p' Hrec; rewrite nat_of_P_xO.
       rewrite inj_mult.
       rewrite Zpos_xO.
       unfold Z.succ.
       rewrite Hrec.
       simpl; auto.
    +  simpl; auto.
 - intros p' Hd; elim Hd;auto.
Qed.

Theorem check_range_correct :
  forall (v:Z)(r:nat)(rz:Z),
  (0 < v)%Z ->
  Z_of_nat (S r) = rz -> check_range v r rz = true ->
  ~ (exists k:nat, k <= (S r) /\ k <> 1 /\ 
                       (exists q:nat, Z.abs_nat v = q*k)).
Proof.
 intros v r; elim r.
 -  intros rz Hlt H1 H2 Hex; case Hex; intros k; case k.
   +  intros (Hle, (Hne1, (q, Heq))).
      rewrite mult_comm in Heq; simpl in Heq.
      rewrite (Zabs_nat_0 _ Heq) in Hlt.
      elim (Z.lt_irrefl 0); assumption.
   +  intros k' (Hle, (Hne1, (q, Heq))).
      inversion Hle.
      assert (H':k'=0).
      * assumption.
      * rewrite H' in Hne1; elim Hne1;auto.
      * assert (H': S k' <= 0) by  assumption.
        inversion H'.
-  intros r' Hrec rz Hlt H1 H2 Hex; case Hex; intros k; case k.
   +  intros (Hle, (Hne1, (q, Heq))).
      rewrite mult_comm in Heq; simpl in Heq.
      rewrite (Zabs_nat_0 _ Heq) in Hlt.
      elim (Z.lt_irrefl 0); assumption.
   +  intros k' (Hle, (Hne1, (q, Heq))).
      inversion Hle.
      rewrite <- H1 in H2. 
      rewrite <- (Z_to_nat_and_back v) in H2.
      assert (Hmod:(Z_of_nat (Z.abs_nat v) mod Z.of_nat (S (S r')) = 0)%Z).
      *  apply verif_divide.
         replace 0 with (Z.abs_nat 0%Z).
         apply Zabs_nat_lt.
         omega.
         simpl; auto.
         auto with arith.
         exists q.
         assert (H': k' = S r') by assumption.
         rewrite <- H';auto.
      *   unfold check_range in H2.
         rewrite Hmod in H2; discriminate H2.
      *  omega.
      *  unfold check_range in H2; fold check_range in H2.
         case_eq ((v mod rz)%Z).
         intros Heqmod.
         rewrite Heqmod in H2.
         discriminate H2.
         intros pmod Heqmod; rewrite Heqmod in H2.
         elim (Hrec (Z.pred rz) Hlt).
         rewrite <- H1.
         rewrite inj_S.
         rewrite inj_S.
         rewrite inj_S.
         rewrite <- Zpred_succ.
         auto.
         assumption.
         exists (S k').
         repeat split;auto.
         exists q; assumption.
         intros p Hmod.
         elim (Z_mod_lt v rz).
         rewrite Hmod.
         unfold Z.le; simpl; intros Hle'; elim Hle';auto.
         rewrite <- H1.
         rewrite inj_S.
         unfold Z.succ.
         generalize (Zle_0_nat (S r')).
         intros; omega.
Qed.

Theorem nat_of_P_Psucc : 
 forall p:positive, nat_of_P (Pos.succ p) = S (nat_of_P p).
Proof.
 intros p; elim p.
 -  simpl; intros p'; rewrite nat_of_P_xO.
    intros Heq; rewrite Heq; rewrite nat_of_P_xI; ring.
 - intros p' Heq; simpl.
   rewrite nat_of_P_xI.
   rewrite nat_of_P_xO;auto.
 -  auto.
Qed.

Theorem nat_to_Z_and_back:
 forall n:nat, Z.abs_nat (Z.of_nat n) = n.
Proof.
 intros n; elim n.
 -  auto.
 - intros n'; simpl; case n'.
  + simpl; auto.
  +  intros n''; simpl; rewrite nat_of_P_Psucc.
     intros Heq; rewrite Heq; auto.
Qed.
 

Theorem check_correct :
  forall p:nat, 0 < p -> check_primality p = true ->
  ~(exists k:nat, k <> 1 /\ k <> p /\ (exists q:nat, p = q*k)).
Proof.
 unfold lt; intros p Hle; elim Hle.
 -  intros Hcp (k, (Hne1, (Hne1bis, (q, Heq))));
   rewrite mult_comm in Heq.
    assert (Hle' : k < 1).
   +  elim (le_lt_or_eq k 1); try(intuition; fail).
      apply divisor_smaller with (2:= Heq); auto.
   + case_eq k.
     intros Heq'; rewrite Heq' in Heq; simpl in Heq; discriminate Heq.
     intros; omega.
 -  intros p' Hlep' Hrec; unfold check_primality.
    assert (H':(exists p'':nat, p' = (S p''))).
    +  inversion Hlep'.
       exists 0; auto.
       eapply ex_intro;eauto.
    +  elim H'; intros p'' Hp''; rewrite Hp''.
       repeat rewrite <- pred_Sn.
       intros Hcr Hex.
       elim check_range_correct with (3:= Hcr).
       rewrite inj_S; generalize (Zle_0_nat (S p'')).
       intros; omega.
       auto.
       elim Hex; intros k (Hne1, (HneSSp'', (q, Heq))); exists k.
       split.
       assert (HkleSSp'': k <= S (S p'')).
       * apply (divisor_smaller (S (S p'')) q).
         auto with arith.
         rewrite mult_comm.
         assumption.
       *  omega.
       * split.
         assumption.
         exists q; now rewrite nat_to_Z_and_back.
Qed.


Theorem prime_2333 :
 ~(exists k:nat, k <> 1 /\ k <> 2333 /\ (exists q:nat, 2333 = q*k)).
Proof.
 Time apply check_correct; auto with arith.
(**Finished transaction in 132. secs (131.01u,0.62s)*)
Time Qed.


Theorem reflection_test :
 forall x y z t u:nat, x+(y+z+(t+u)) = x+y+(z+(t+u)).
Proof.
 intros; repeat rewrite plus_assoc; auto.
Qed.

Inductive bin : Set := node : bin->bin->bin | leaf : nat->bin.

Fixpoint flatten_aux (t fin:bin){struct t} : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
  | x => node x fin
  end.

Fixpoint flatten (t:bin) : bin :=
  match t with
  | node t1 t2 => flatten_aux t1 (flatten t2)
  | x => x
  end.

Compute 
  flatten
     (node (leaf 1) (node (node (leaf 2)(leaf 3)) (leaf 4))).

Fixpoint bin_nat (t:bin) : nat :=
  match t with
  | node t1 t2 => bin_nat t1 + bin_nat t2
  | leaf n => n
  end.

Eval lazy beta iota delta [bin_nat] in
 (bin_nat
   (node (leaf 1) (node (node (leaf 2) (leaf 3)) (leaf 4)))).

Theorem flatten_aux_valid :
 forall t t':bin, bin_nat t + bin_nat t' = bin_nat (flatten_aux t t').
Proof.
 intros t; elim t; simpl; auto.
 intros t1 IHt1 t2 IHt2 t'; rewrite <- IHt1; rewrite <- IHt2.
 rewrite plus_assoc; trivial.
Qed.

Theorem flatten_valid : forall t:bin, bin_nat t = bin_nat (flatten t).
Proof.
 intros t; elim t; simpl; auto.
 intros t1 IHt1 t2 IHt2; rewrite <- flatten_aux_valid; rewrite <- IHt2.
 trivial.
Qed.

Theorem flatten_valid_2 :
  forall t t':bin, bin_nat (flatten t) = bin_nat (flatten t')->
  bin_nat t = bin_nat t'.
Proof.
 intros; rewrite (flatten_valid t); rewrite (flatten_valid t');
 auto.
Qed.

Theorem reflection_test' :
 forall x y z t u:nat, x+(y+z+(t+u))=x+y+(z+(t+u)).
Proof.
 intros.
 change
   (bin_nat
      (node (leaf x)
         (node (node (leaf y) (leaf z))
               (node (leaf t)(leaf u)))) =
    bin_nat
      (node (node (leaf x)(leaf y))
         (node (leaf z)
               (node (leaf t)(leaf u))))).
 apply flatten_valid_2; auto.
Qed.

Ltac model v :=
  match v with
  | (?X1 + ?X2) =>
    let r1 := model X1 
              with r2 := model X2 in constr:(node r1 r2)
  | ?X1 => constr:(leaf X1)
  end.

Ltac assoc_eq_nat :=
  match goal with
  | [ |- (?X1 = ?X2 :>nat) ] =>
   let term1 := model X1 with term2 := model X2 in
   (change (bin_nat term1 = bin_nat term2);
    apply flatten_valid_2;
    lazy beta iota zeta delta [flatten flatten_aux bin_nat]; 
    auto)
  end.


Theorem reflection_test'' :
 forall x y z t u:nat, x+(y+z+(t+u)) = x+y+(z+(t+u)).
Proof.
 intros; assoc_eq_nat.
Qed.

Section assoc_eq.
Variables (A : Type)(f : A->A->A)
  (assoc : forall x y z:A, f x (f y z) = f (f x y) z).

Fixpoint bin_A (l:list A)(def:A)(t:bin){struct t} : A :=
  match t with
  | node t1 t2 => f (bin_A l def t1)(bin_A l def t2)
  | leaf n => nth n l def
  end.

Theorem flatten_aux_valid_A :
 forall (l:list A)(def:A)(t t':bin),
 f (bin_A l def t)(bin_A l def t') = bin_A l def (flatten_aux t t').
Proof.
 intros l def t; elim t; simpl; auto.
 intros t1 IHt1 t2 IHt2 t';  rewrite <- IHt1; rewrite <- IHt2.
 symmetry; apply assoc.
Qed.

Theorem flatten_valid_A :
 forall (l:list A)(def:A)(t:bin),
   bin_A l def t = bin_A l def (flatten t).
Proof.
 intros l def t; elim t; simpl; trivial.
 intros t1 IHt1 t2 IHt2; rewrite <- flatten_aux_valid_A; now rewrite <- IHt2.
Qed.

Theorem flatten_valid_A_2 :
 forall (t t':bin)(l:list A)(def:A),
   bin_A l def (flatten t) = bin_A l def (flatten t')->
   bin_A l def t = bin_A l def t'. 
Proof.
 intros t t' l def Heq.
 rewrite (flatten_valid_A l def t); now rewrite (flatten_valid_A l def t').
Qed.

End assoc_eq.

Ltac term_list f l v :=
  match v with
  | (f ?X1 ?X2) =>
    let l1 := term_list f l X2 in term_list f l1 X1
  | ?X1 => constr:(cons X1 l)
  end.

Ltac compute_rank l n v :=
  match l with
  | (cons ?X1 ?X2) =>
    let tl := constr:(X2) in
    match constr:(X1 = v) with
    | (?X1 = ?X1) => n
    | _ => compute_rank tl (S n) v
    end
  end.

Ltac model_aux l f v :=
  match v with
  | (f ?X1 ?X2) =>
    let r1 := model_aux l f X1 with r2 := model_aux l f X2 in
      constr:(node r1 r2)
  | ?X1 => let n := compute_rank l 0 X1 in constr:(leaf n)
  | _ => constr:(leaf 0)
  end.

Ltac model_A A f def v :=
  let l := term_list f (nil (A:=A)) v in
  let t := model_aux l f v in
  constr:(bin_A A f l def t).

Ltac assoc_eq A f assoc_thm :=
  match goal with
  | [ |- (@eq A ?X1 ?X2) ] =>
  let term1 := model_A A f X1 X1 
  with term2 := model_A A f X1 X2 in
  (change (term1 = term2);
   apply flatten_valid_A_2 with (1 := assoc_thm); auto)
  end.

Theorem reflection_test3 :
 forall x y z t u:Z, (x*(y*z*(t*u)) = x*y*(z*(t*u)))%Z.
Proof.
 intros; assoc_eq Z Zmult Zmult_assoc.
Qed.


Fixpoint nat_le_bool (n m:nat){struct m} : bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n, S m => nat_le_bool n m
  end.

Fixpoint insert_bin (n:nat)(t:bin){struct t} : bin :=
  match t with
  | leaf m => match nat_le_bool n m with
              | true => node (leaf n)(leaf m)
              | false => node (leaf m)(leaf n)
              end
  | node (leaf m) t' => match nat_le_bool n m with
                        | true => node (leaf n) t
                        | false => 
                            node (leaf m)(insert_bin n t')
                        end
  | t => node (leaf n) t
  end.

Fixpoint sort_bin (t:bin) : bin :=
  match t with
  | node (leaf n) t' => insert_bin n (sort_bin t')
  | t => t
  end.




Section commut_eq.
(** this section contains some primed versions of previous constructions
   (for avoiding Reset commands)

*)

 Variables (A : Type)(f : A->A->A).
 Hypothesis comm : forall x y:A, f x y = f y x.
 Hypothesis assoc : forall x y z:A, f x (f y z) = f (f x y) z.

 Fixpoint bin_A' (l:list A)(def:A)(t:bin){struct t} : A :=
   match t with
   | node t1 t2 => f (bin_A' l def t1)(bin_A' l def t2)
   | leaf n => nth n l def
   end.

 Theorem flatten_aux_valid_A' :
  forall (l:list A)(def:A)(t t':bin),
   f (bin_A' l def t)(bin_A' l def t') = bin_A' l def (flatten_aux t t').
 Proof.
  intros l def t; elim t; simpl; auto.
  intros t1 IHt1 t2 IHt2 t';  rewrite <- IHt1; rewrite <- IHt2.
  symmetry; apply assoc.
 Qed.

 Theorem flatten_valid_A' :
  forall (l:list A)(def:A)(t:bin),
    bin_A' l def t = bin_A' l def (flatten t).
 Proof.
  intros l def t; elim t; simpl; trivial.
  intros t1 IHt1 t2 IHt2; rewrite <- flatten_aux_valid_A'; rewrite <- IHt2.
  trivial.
 Qed.

Theorem flatten_valid_A_2' :
 forall (t t':bin)(l:list A)(def:A),
   bin_A' l def (flatten t) = bin_A' l def (flatten t')->
   bin_A' l def t = bin_A' l def t'. 
Proof.
 intros t t' l def Heq.
 rewrite (flatten_valid_A' l def t); rewrite (flatten_valid_A' l def t').
 trivial.
Qed.

Theorem insert_is_f : forall (l:list A)(def:A)(n:nat)(t:bin),
   bin_A' l def (insert_bin n t) = 
   f (nth n l def) (bin_A' l def t).
Proof.
 intros l def n t; elim t.
 intros t1; case t1.
 intros t1' t1'' IHt1 t2 IHt2.
 simpl.
 auto.
 intros n0 IHt1 t2 IHt2.
 simpl.
 case (nat_le_bool n n0).
 simpl.
 auto.
 simpl.
 rewrite IHt2.
 repeat rewrite assoc; rewrite (comm (nth n l def)); auto.
 simpl.
 intros n0; case (nat_le_bool n n0); auto.
 rewrite comm; auto.
Qed.

Theorem sort_eq : forall (l:list A)(def:A)(t:bin),
    bin_A' l def (sort_bin t) = bin_A' l def t.  
Proof.
 intros l def t; elim t.
 intros t1 IHt1; case t1.
 auto.
 intros n t2 IHt2; simpl; rewrite insert_is_f.
 rewrite IHt2; auto.
 auto.
Qed.


Theorem sort_eq_2 :
 forall (l:list A)(def:A)(t1 t2:bin),
   bin_A' l def (sort_bin t1) = bin_A' l def (sort_bin t2)->
   bin_A' l def t1 = bin_A' l def t2.  
Proof.
 intros l def t1 t2.
 rewrite <- (sort_eq l def t1); rewrite <- (sort_eq l def t2).
 trivial.
Qed.

End commut_eq.


Ltac term_list' f l v :=
  match v with
  | (f ?X1 ?X2) =>
    let l1 := term_list' f l X2 in term_list' f l1 X1
  | ?X1 => constr:(cons X1 l)
  end.

Ltac compute_rank' l n v :=
  match l with
  | (cons ?X1 ?X2) =>
    let tl := constr:(X2) in
    match constr:(X1 = v) with
    | (?X1 = ?X1) => n
    | _ => compute_rank' tl (S n) v
    end
  end.

Ltac model_aux' l f v :=
  match v with
  | (f ?X1 ?X2) =>
    let r1 := model_aux' l f X1 with r2 := model_aux' l f X2 in
      constr:(node r1 r2)
  | ?X1 => let n := compute_rank' l 0 X1 in constr:(leaf n)
  | _ => constr:(leaf 0)
  end.

Ltac comm_eq' A f assoc_thm comm_thm :=
  match goal with
  | [ |- (?X1 = ?X2 :>A) ] =>
    let l := term_list' f (nil (A:=A)) X1 in
    let term1 := model_aux' l f X1 
    with term2 := model_aux' l f X2 in
    (change (bin_A' A f l X1 term1 = bin_A' A f l X1 term2);
      apply flatten_valid_A_2' with (1 := assoc_thm);
      apply sort_eq_2 with (1 := comm_thm)(2 := assoc_thm); 
      auto)
  end.

Theorem reflection_test4 : forall x y z:Z, (x+(y+z) = (z+x)+y)%Z.
Proof.
 intros x y z. comm_eq' Z Zplus Zplus_assoc Zplus_comm.
Qed.

