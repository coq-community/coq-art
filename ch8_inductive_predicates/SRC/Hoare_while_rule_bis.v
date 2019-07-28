Require Export ZArith.

Section little_semantics.
Variables Var aExp bExp : Set.
Inductive inst : Set :=
| Skip : inst
| Assign : Var->aExp->inst
| Sequence : inst->inst->inst
| WhileDo : bExp->inst->inst.
Variables
  (state : Set)
  (update : state->Var->Z -> option state)
  (evalA : state->aExp -> option Z)
  (evalB : state->bExp -> option bool).
Inductive exec : state->inst->state->Prop :=
| execSkip : forall s:state, exec s Skip s
| execAssign :
   forall (s s1:state)(v:Var)(n:Z)(a:aExp),
     evalA s a = Some n -> update s v n = Some s1 ->
     exec s (Assign v a) s1
| execSequence :
   forall (s s1 s2:state)(i1 i2:inst),
    exec s i1 s1 -> exec s1 i2 s2 ->
    exec s (Sequence i1 i2) s2
| execWhileFalse :
   forall (s:state)(i:inst)(e:bExp),
    evalB s e = Some false -> exec s (WhileDo e i) s
| execWhileTrue :
   forall (s s1 s2:state)(i:inst)(e:bExp),
    evalB s e = Some true ->
    exec s i s1 ->
    exec s1 (WhileDo e i) s2 ->
    exec s (WhileDo e i) s2.

(* Instead of using an equality to control the relation between the
   arguments of the inductive predicate and the subterms that appear
   in the rest of the statement, we replace each instance of these
   subterms with applications of projection functions to the whole
   term.  These projections are meaningful as projections only when
   the term given as argument is a while construct.  For the other
   cases, we need a default value.  *)
   

Definition get_test_from_while (b:bExp)(i:inst) :=
  match i with
    WhileDo b' i' => b'
  | _ => b
  end.

(* When the result is an instruction, the default value can be the
   whole instruction. *)

Definition get_body_from_while (i:inst) :=
  match i with
    WhileDo b' i' => i'
  | _ => i
  end.

(* The induction step generates bad cases that we will discard thanks
   to this function. *)

Definition is_while (i:inst) :=
  match i with WhileDo b' i' => True | _ => False end.

(* We do the real proof in this auxiliary lemma, where data
   is prepared with the help of the projection functions and the
   premises are placed in the right order. *)

Lemma HoareWhileRule_aux :
 forall (P:state->Prop)(b:bExp)(i:inst)(s s':state),
   exec s (WhileDo b i) s' ->
   (forall s1 s2:state,
      P s1 ->
      evalB s1 (get_test_from_while b (WhileDo b i)) = Some true -> 
      exec s1 (get_body_from_while (WhileDo b i)) s2 -> P s2)->
   P s -> 
   P s' /\ evalB s' (get_test_from_while b (WhileDo b i)) = Some false.
Proof.
 intros P b i s s' Hexec.
 generalize (I:is_while (WhileDo b i)).
 elim Hexec;try(auto;simpl; intros; contradiction).
 simpl.
 intros s0 s1 s2 i0 e Heval Hexec1 IH1 Hexec2 IH2 _ IH_invariant HP.
 apply IH2;auto.
 apply IH_invariant with s0;auto.
Qed.

(* The main theorem is a simple application of the lemma. *)

Theorem HoareWhileRule :
 forall (P:state->Prop)(b:bExp)(i:inst)(s s':state),
   (forall s1 s2:state,
      P s1 -> evalB s1 b = Some true -> exec s1 i s2 -> P s2)->
   P s -> exec s (WhileDo b i) s' ->
   P s' /\ evalB s' b = Some false.
Proof.
 intros P b i s s' H_invariant HP Hexec.
 apply (HoareWhileRule_aux P b i s s');simpl; auto.
Qed.

End little_semantics.
