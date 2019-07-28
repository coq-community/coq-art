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

Theorem HoareSequenceRule :
 forall (P1 P2 P3:state->Prop)(i1 i2:inst)(s s':state),
  (forall s1 s2, exec s1 i1 s2 -> P1 s1 -> P2 s2)->
  (forall s1 s2, exec s1 i2 s2 -> P2 s1 -> P3 s2)->
  exec s (Sequence i1 i2) s' -> P1 s -> P3 s'.
Proof.
 intros P1 P2 P3 i1 i2 s s' HP12 HP23 Hexec Hp1.
 inversion Hexec.
 match goal with
   id1 : exec s i1 _ , id2 : exec _ i2 s' |- _ =>
     try (apply (HP23 _ _ id2); apply (HP12 _ _ id1); assumption)
 end.
Qed.

End little_semantics.