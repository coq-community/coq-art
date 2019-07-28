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

Theorem infinite_loop_aux :
 forall (s s':state)(i:inst),
   exec s i s' -> 
   forall b, i = (WhileDo b Skip) -> evalB s b = Some true -> False.
Proof.
 intros s s' i Hexec; elim Hexec; try (intros; discriminate).
 - intros s0 i0 e Heval b Heq; injection Heq; intros Heq1 Heq2; subst;
   rewrite Heval; intros; discriminate.
 -  intros s0 s1 s2 i0 e Heval Hexeci0 _ Hexecw IHw b Heq; injection Heq;
    intros Heq1 Heq2 _; subst.
     apply (IHw b); trivial.
     inversion Hexeci0; subst; trivial.
Qed.

Theorem infinite_loop :
 forall (s s':state)(b:bExp),
   exec s (WhileDo b Skip) s' -> evalB s b = Some true -> False.
Proof.
 intros s s' b Hexec Heval.
 apply (infinite_loop_aux s s' (WhileDo b Skip) Hexec b); trivial.
Qed.


End little_semantics.