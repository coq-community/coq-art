
Require Export ZArith.
Require Export Zwf.
Require Export Inverse_Image.
Require Export Wellfounded.
Require Import Extraction.

Section little_abstract_semantics.
Variables 
  (Var aExp bExp state : Set) 
  (evalA : state -> aExp -> option Z)
  (evalB : state -> bExp -> option bool)
  (update : state -> Var -> Z -> option state).
 
Inductive inst : Set :=
  | Skip : inst
  | Assign : Var -> aExp -> inst
  | Scolon : inst -> inst -> inst
  | WhileDo : bExp -> inst -> inst.

Arguments Some [A] _.

(* The semantics of the language is given in chapter 7. *)
 
Inductive exec : state -> inst -> state -> Prop :=
  | execSkip : forall s:state, exec s Skip s
  | execAssign :
      forall (s s1:state) (v:Var) (n:Z) (a:aExp),
        evalA s a = Some n ->
        update s v n = Some s1 -> exec s (Assign v a) s1
  | execScolon :
      forall (s s1 s2:state) (i1 i2:inst),
        exec s i1 s1 -> exec s1 i2 s2 -> exec s (Scolon i1 i2) s2
  | execWhileFalse :
      forall (s:state) (i:inst) (e:bExp),
        evalB s e = Some false -> exec s (WhileDo e i) s
  | execWhileTrue :
      forall (s s1 s2:state) (i:inst) (e:bExp),
        evalB s e = Some true ->
        exec s i s1 -> exec s1 (WhileDo e i) s2 -> exec s (WhileDo e i) s2.
(* We need to use the evaluation functions as if they were total.  extract_option
   makes them total by adding a default value. *)
 
Definition extract_option {A:Type} (x:option A) (def:A) : A :=
  match x with
  | None => def
  | Some v => v
  end.

(* When a while loop contains a variable that is decreased at each
  step and tested against a bound, it is obvious that this loop will
  terminate.  We consider such loops are "for" loops.*)
 
Inductive forLoops : inst -> Prop :=
  | aForLoop :
      forall (e:bExp) (i:inst) (variant:aExp),
        (forall s s':state,
           evalB s e = Some true ->
           exec s i s' ->
           Zwf 0 (extract_option (evalA s' variant) 0%Z)
             (extract_option (evalA s variant) 0%Z)) ->
        forLoops i -> forLoops (WhileDo e i)
  | assignFor : forall (v:Var) (e:aExp), forLoops (Assign v e)
  | skipFor : forLoops Skip
  | scolonFor :
      forall i1 i2:inst,
        forLoops i1 -> forLoops i2 -> forLoops (Scolon i1 i2).

(* Following a suggestion by C. McBride and J. McKinna in "The view from the left. "
  we use an auxillary function to perform case analysis instead of using dependent
  pattern-matching construct.  This relies on a "sister type" where pattern matching
  information is gathered in an equality. *)
 
Inductive inst_cases_type (i:inst) : Set :=
  | is_Skip : i = Skip -> inst_cases_type i
  | is_assign : forall (v:Var) (e:aExp), i = Assign v e -> inst_cases_type i
  | is_seq : forall i1 i2:inst, i = Scolon i1 i2 -> inst_cases_type i
  | is_while :
      forall (b:bExp) (i':inst), i = WhileDo b i' -> inst_cases_type i.

(* We avoid dependent pattern matching in the main function, but of course
  this auxillary function has to do the dirty work. *)
 
Definition inst_cases (i:inst) : inst_cases_type i :=
  match i as x return inst_cases_type x with
  | Assign v e => is_assign (Assign v e) v e (refl_equal (Assign v e))
  | Scolon i1 i2 => is_seq (Scolon i1 i2) i1 i2 (refl_equal (Scolon i1 i2))
  | WhileDo b i => is_while (WhileDo b i) b i (refl_equal (WhileDo b i))
  | Skip => is_Skip Skip (refl_equal Skip)
  end.

(* We are going to use recursion on an ad-hoc predicate to define our function.
  This requires that we prove inversion lemmas by case analysis and make sure
  these lemmas are transparent. *)
 
Theorem forLoops_Inv_seq1 :
 forall i:inst,
   forLoops i -> forall i1 i2:inst, i = Scolon i1 i2 -> forLoops i1.
Proof.
intros i h; case h; try (intros; discriminate).
intros i1 i2 H H0 i0 i3 H1; injection H1.
intros heq2 heq1; rewrite <- heq1; assumption.
Defined.
 
Theorem forLoops_Inv_seq2 :
 forall i:inst,
   forLoops i -> forall i1 i2:inst, i = Scolon i1 i2 -> forLoops i2.
Proof.
intros i h; case h; try (intros; discriminate).
intros i1 i2 H H0 i0 i3 H1; injection H1.
intros heq2 heq1; rewrite <- heq2; assumption.
Defined.
 
Theorem forLoops_Inv_while2 :
 forall i:inst,
   forLoops i -> forall (b:bExp) (i':inst), i = WhileDo b i' -> forLoops i'.
Proof.
 intros i h; case h; try (intros; discriminate).
 intros e i0 variant H H0 b i' H1; injection H1.
 intros heq2 heq1; rewrite <- heq2; assumption.
Defined.
 
Inductive exec_or_not (s:state) (i:inst) : Set :=
  | result : forall s':state, exec s i s' -> exec_or_not s i
  | no_result : (forall s':state, ~ exec s i s') -> exec_or_not s i.

Parameter
  exec_det :
    forall (s s' s'':state) (i:inst), exec s i s' -> exec s i s'' -> s' = s''.

(* We invent a new relation indexed by instructions and boolean expressions.
  If the indexes are i and b, we say that two states s1 and s2 are related if
  s1 is the result of executing i from state s2 and if b evaluates to true in b.
  Intuitively, i will be used as the body of a while loop construct and b as the
  halting condition for this loop.  In general, this relation is NOT well-founded.*)
 
Definition state_loop_order (i:inst) (b:bExp) (s1 s2:state) : Prop :=
  evalB s2 b = Some true /\ exec s2 i s1.

(* If the loop (WhileDo b i) is a "for" loop, then there is something
  that decreases each time the loop body is executed (by definition).
  This makes it possible to prove that the relation (state_loop_order i b) is
  well-founded.*)
 
Theorem state_loop_order_wf :
 forall (b:bExp) (i:inst),
   forLoops (WhileDo b i) -> well_founded (state_loop_order i b).
Proof. 
  intros b i h; inversion h.
  apply wf_incl with
  (fun s1 s2:state =>
     Zwf 0 (extract_option (evalA s1 variant) 0%Z)
         (extract_option (evalA s2 variant) 0%Z)).
   unfold Relation_Definitions.inclusion in |- *.
   unfold state_loop_order in |- *; intros x y [H3 H4].
   apply H1.
   apply H3.
   apply H4.
   apply
     (wf_inverse_image state Z (Zwf 0)
                       (fun s:state => extract_option (evalA s variant) 0%Z)
                       (Zwf_well_founded 0)).
Qed.

(* If i is the Skip instruction, it is always possible to decide whether
   executing i will succeed or not.*)
 
Lemma exec_skip : forall (i:inst) (s:state), i = Skip -> exec_or_not s i.
Proof. 
  intros i s heq;
 exact (result s i s (eq_ind_r (fun j:inst => exec s j s) (execSkip s) heq)).
Defined.

(* If i is an assignment, it is always possible to decide whether
  executing i will succeed or not.*)
 
Lemma exec_assign :
 forall (i:inst) (s:state) (v:Var) (e:aExp),
   i = Assign v e -> exec_or_not s i.
Proof. 
 intros i s v e heq; case_eq (evalA s e).
 - intros v' heqa; case_eq (update s v v').
   + intros s' Hequ; apply (result s i s').
     rewrite heq.
     apply execAssign with v'; assumption.
   + intros heq_None; apply no_result.
     rewrite heq; intros s' H; inversion H.
     rewrite heqa in H3; injection H3.
     intros heqv'; rewrite heqv' in heq_None; rewrite H5 in heq_None.
     discriminate.
 - intros heq_None; apply no_result.
   rewrite heq; intros s' H; inversion H.
   rewrite H3 in heq_None; discriminate.
Defined.

(* If i is a sequence of two instructions and we already have two functions
   that can decide the success of execution for these instructions, then
   deciding the success for these instructions is an easy matter.*)
 
Lemma exec_sequence :
 forall (i:inst) (s:state) (i1 i2:inst),
   i = Scolon i1 i2 ->
   forall (f1:forall s:state, exec_or_not s i1)
     (f2:forall s:state, exec_or_not s i2), exec_or_not s i.
Proof. 
 intros i s i1 i2 heq f1 f2.
 case (f1 s).
 - intros s1 Hexec1; case (f2 s1).
   + intros s2 Hexec2; apply (result s i s2).
     rewrite heq; apply execScolon with s1; assumption.
   + intros Hnot; apply no_result.
     rewrite heq.
     intros s'; red in |- *; intros H; inversion H.
     elim (Hnot s').
     rewrite (exec_det s s1 s2 i1); assumption.
 - intros Hnot; apply no_result.
   rewrite heq.
   intros s' H; inversion H.
   elim (Hnot s1); assumption.
Defined.


(** Now comes the difficult part.  If i is a loop, the body of which is i',
  then it is in general not possible to decide whether the execution will
  succeed or not.  On the other hand, if the loop is a "for" loop and we
  are given a function that can decide whether executing i' succeeds, then
  we can use well-founded recursion to define a function that repeats
  the body as many times until execution fails or succeeds.  This is
  guaranteed to terminate thanks to the proof of state_loop_order_wf. *)
 
Lemma exec_forLoop :
 forall (i i':inst) (b:bExp) (s:state),
   i = WhileDo b i' ->
   forLoops (WhileDo b i') ->
   forall f:forall s:state, exec_or_not s i', exec_or_not s i.
Proof. 
 intros i i' b s heq h' f;
  apply
    (well_founded_induction (state_loop_order_wf b i' h')
                            (fun s:state => exec_or_not s i)).
 intros s0 loop_again.
 case_eq (evalB s0 b).
 -  intros vb; case vb.
    + intros heqCond; elim (f s0).
      * intros s1 Hexeci'; elim (loop_again s1).
       intros s2 Hexeci; apply (result s0 i s2).
       rewrite heq.
       apply execWhileTrue with (s1 := s1); try assumption.
       rewrite <- heq.
       apply Hexeci.
       intros Hnot; apply no_result.
       rewrite heq; intros s' H; inversion H.
       rewrite H2 in heqCond.
       rewrite heqCond in H4.
       discriminate H4.
       elim (Hnot s').
       rewrite (exec_det s0 s1 s3 i'); try assumption.
       rewrite heq.
       assumption.
       split; assumption.
    * intros Hnot; apply no_result.
      rewrite heq; intros s' H; inversion H.
      rewrite H2 in heqCond; rewrite H4 in heqCond.
      discriminate.
      elim (Hnot s2); assumption.
    + intros heqCond; apply (result s0 i s0).
      rewrite heq.
      apply execWhileFalse; assumption.
 - intros heqCond; apply no_result.
   rewrite heq.
   intros s' H; inversion H.
   rewrite H2 in heqCond.
   rewrite H4 in heqCond; discriminate heqCond.
   rewrite H2 in heqCond.
discriminate heqCond.
Defined.

(*This is the main recursive function.  Note that its definition relies on
  the advanced technique of recursion on an ad-hoc predicate.  In fact, the
  whole execution process relies on a nested recursion, since loops are 
  executed using well-founded recursion inside the exec_forLoop function.*)
 
Definition exl : forall i:inst, forLoops i -> forall s:state, exec_or_not s i.
refine
 (fix exl (i:inst) (h:forLoops i) {struct h} :
    forall s:state, exec_or_not s i :=
    fun s =>
      match inst_cases i with
      | is_Skip _ heq => exec_skip i s heq
      | is_assign _ v e heq => exec_assign i s v e heq
      | is_seq _ i1 i2 heq => exec_sequence i s i1 i2 heq _ _
      | is_while _ b i' heq => exec_forLoop i i' b s heq _ _
      end).
Proof.
  exact (exl i1 (forLoops_Inv_seq1 i h i1 i2 heq)).
  exact (exl i2 (forLoops_Inv_seq2 i h i1 i2 heq)).
  rewrite <- heq; assumption.
  exact (exl i' (forLoops_Inv_while2 i h b i' heq)).
Defined.
(* This function has the type required in the exercise. *)
 
Definition execute_loops :
  forall (s:state) (i:inst),
    forLoops i ->
    {s' : state | exec s i s'} + {(forall s':state, ~ exec s i s')}.
Proof.
  intros s i h; elim (exl i h s).
  - left; exists s'; assumption.
  -right; assumption.
Defined.
 
End little_abstract_semantics.

(* This is not part of the exercise. *)

(* Here we want to instantiate the various types to build a minimal
   programming language and show we can build a program that satisfies
   the "forLoops" predicate. *)

Arguments Some [A] _.

Require Export List.
Require Export Arith.
Require Export Compare_dec.
Require Export Omega.

Inductive aExp : Set :=
  | aPlus : aExp -> aExp -> aExp
  | aNum : Z -> aExp
  | aVar : nat -> aExp.

Inductive bExp : Set :=
    bGt : aExp -> aExp -> bExp.

Definition state := list Z.

Fixpoint lookup (idx:nat) (s:state) {struct idx} : 
 option Z :=
  match idx, s with
  | O, a :: _ => Some a
  | S p, _ :: tl => lookup p tl
  | _, _ => None (A:=Z)
  end.

Fixpoint evalA (s:state) (e:aExp) {struct e} : option Z :=
  match e with
  | aPlus e1 e2 =>
      match evalA s e1, evalA s e2 with
      | Some n1, Some n2 => Some (n1 + n2)%Z
      | _, _ => None (A:=Z)
      end
  | aNum n => Some n
  | aVar n => lookup n s
  end.

Definition evalB (s:state) (e:bExp) : option bool :=
  match e with
  | bGt e1 e2 =>
      match evalA s e1, evalA s e2 with
      | Some n1, Some n2 =>
          match Z_le_gt_dec n1 n2 with
          | left _ => Some false
          | right _ => Some true
          end
      | _, _ => None (A:=bool)
      end
  end.

Fixpoint update (s:state) (n:nat) (x:Z) {struct n} : 
 option state :=
  match s, n with
  | a :: tl, O => Some (x :: tl)
  | a :: tl, S p =>
      match update tl p x with
      | Some tl' => Some (a :: tl')
      | _ => None (A:=state)
      end
  | _, _ => None (A:=state)
  end.

Arguments Assign [Var aExp bExp].
Arguments WhileDo [Var aExp bExp].
Arguments Scolon [Var aExp bExp].

Example fact3 :=
  Scolon (Assign 1 (aNum 3))
    (Scolon (Assign 2 (aNum 1))
       (WhileDo (bGt (aVar 1) (aNum 0))
          (Scolon (Assign 0 (aVar 1))
             (Scolon (Assign 1 (aPlus (aVar 1) (aNum (-1))))
                (Scolon (Assign 3 (aVar 2))
                   (Scolon (Assign 2 (aNum 0))
                      (WhileDo (bGt (aVar 0) (aNum 0))
                         (Scolon (Assign 0 (aPlus (aVar 0) (aNum (-1))))
                            (Assign 2 (aPlus (aVar 2) (aVar 3))))))))))).

Fixpoint noAssign (n:nat) (i:inst nat aExp bExp) {struct i} : bool :=
  match i with
  | Skip _ _ _  => true
  | Scolon  i1 i2 =>
      match noAssign n i1 with
      | true => noAssign n i2
      | false => false
      end
  | WhileDo b i' => noAssign n i'
  | Assign v e =>
      match eq_nat_dec v n with
      | left _ => false
      | right _ => true
      end
  end.

Theorem lookup_update_eq :
 forall (n:nat) (s s':state) (v:Z),
   update s n v = Some s' -> lookup n s' = Some v.
Proof. 
simple induction n.
- intros s; case s.
  + intros; discriminate.
  + simpl in |- *; intros z tl s' v Heq; injection Heq; intros Heq1;
    rewrite <- Heq1; trivial.
- intros p Hrec s; case s; simpl in |- *; try (intros; discriminate).
  intros z l s' v; generalize (fun s':state => Hrec l s' v).
  case (update l p v); simpl in |- *; try (intros; discriminate).
  intros s'0 Hrec' Heq; injection Heq; intros Heq1; rewrite <- Heq1;
 simpl in |- *; rewrite Hrec'; auto.
Qed.

Theorem lookup_update_diff :
 forall (n m:nat) (s s':state) (v:Z),
   update s n v = Some s' -> n <> m -> lookup m s' = lookup m s.
Proof. 
 simple induction n.
 - intros m; case m.
   + intros s s' v H H1; elim H1; auto.
   + intros m' s; case s; simpl in |- *; try (intros; discriminate).
     * intros z tl s' v Heq; injection Heq; intros Heq1; now rewrite <- Heq1.
 - intros p Hrec m; case m; simpl in |- *.
   + intros s; case s; simpl in |- *; try (intros; discriminate).
     intros z l s' v; case (update l p v); simpl in |- *;
     try (intros; discriminate).
     intros s'0 Heq; injection Heq; intros Heq1; now rewrite <- Heq1.
   + intros m' s; case s; simpl in |- *; try (intros; discriminate).
     intros z l s' v; generalize (fun s':state => Hrec m' l s' v);
     case (update l p v); try (intros; discriminate).
     intros s'0 Hrec' Heq; injection Heq; intros Heq1; rewrite <- Heq1.
     intros Hneq; apply Hrec'; auto with arith.
Qed.

Theorem noAssign_noChange :
 forall (n:nat) (i:inst nat aExp bExp),
   noAssign n i = true ->
   forall s s':state,
     exec nat aExp bExp state evalA evalB update s i s' ->
     evalA s (aVar n) = evalA s' (aVar n).
Proof. 
  intros n i Heq s s' Hexec; generalize n Heq; clear Heq n;  elim Hexec.
  -  auto.
  - simpl in |- *;
    intros s0 s1 v n' a Heval Hupdate n; case (eq_nat_dec v n).
    + discriminate.
    + intros; symmetry  in |- *; apply lookup_update_diff with v n'; auto.
  - simpl in |- *; intros s0 s1 s2 i1 i2 Hex1 Hrec1 Hex2 Hrec2 n.
    generalize (Hrec1 n) (Hrec2 n); clear Hrec1 Hrec2.
    case (noAssign n i1); simpl in |- *; try (intros; discriminate).
    case (noAssign n i2); simpl in |- *; try (intros; discriminate).
    transitivity (lookup n s1); auto.
 - auto.
 - simpl in |- *; intros s0 s1 s2 i' b Heval Hex1 Hrec1 Hex2 Hrec2 n;
   generalize (Hrec1 n) (Hrec2 n); clear Hrec1 Hrec2.
   intros; transitivity (lookup n s1); auto.
Qed.

Theorem forLoops_fact3 :
 forLoops nat aExp bExp state evalA evalB update fact3.
Proof.
 unfold fact3 in |- *; repeat constructor.
 apply aForLoop with (aVar 1).
 intros s; case s.
 -  intros s' Hevgt1 Hexec1; inversion Hexec1.
    inversion H2; simpl in H10; discriminate.
 -  intros v0 s0; case s0.
    +  intros s' Hevgt1 Hexec1; inversion Hexec1.
       inversion H2.
       simpl in H8; discriminate.
    +  intros v1 s1 s' Hevgt1 Hexec1; inversion Hexec1.
       inversion H2.
       simpl in H8.
       simpl in H10.
       injection H8; clear H8; intros H8.
       subst v1; clear Hexec1; inversion H4.
       rewrite <- noAssign_noChange with (2 := H15).
       *  inversion H13.
          simpl in H19.
          injection H10.
          intros Heq1.
          rewrite <- Heq1 in H19, H21.
          injection H19; clear H19; intros H19.
          rewrite <- H19 in H21; simpl in H21; injection H21.
          intros Heq2; rewrite <- Heq2; simpl in |- *.
          unfold Zwf in |- *; auto with zarith.
          inversion Hevgt1.
          generalize H23; 
            case (Z_le_gt_dec n 0); simpl in |- *; try (intros; discriminate).
          intros; omega.
       *  simpl in |- *; auto.
 - repeat constructor.
   apply aForLoop with (aVar 0).
  +  intros s s'; lazy beta iota zeta delta [evalB] in |- *; fold evalB in |- *.
     intros Hevgt Hexec; inversion Hexec.
     inversion H2.
     rewrite <- noAssign_noChange with (2 := H4).
     *  lazy beta iota zeta delta [evalA] in H8; fold evalA in H8.
        generalize H8; clear H8; case_eq (lookup 0 s).
        intros z Hlk H8; injection H8; clear H8; intros H8.
        lazy beta iota zeta delta [evalA] in |- *.
        rewrite lookup_update_eq with (1 := H10).
        rewrite Hlk; rewrite <- H8.
        generalize Hevgt; lazy beta iota zeta delta [evalA] in |- *.
        rewrite Hlk.
        case (Z_le_gt_dec z 0); simpl in |- *; try (intros; discriminate).
        unfold Zwf in |- *; intros; omega.
        intros; discriminate.
     * simpl in |- *; auto.
+ repeat constructor.
Qed.

Definition execute_loops2 :=
  execute_loops nat aExp bExp state evalA evalB update.

Definition value :=
  execute_loops2 (0%Z :: 0%Z :: 0%Z :: 0%Z :: nil) fact3 forLoops_fact3.

(* We use extracted code to test the value of our program instead of
  evaluating inside Coq *)

Extraction "execute_loops" execute_loops2 fact3 value.

 
