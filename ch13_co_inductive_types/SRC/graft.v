Require Export Ltree.

CoFixpoint graft {A:Type} (t t':LTree A) : LTree A :=
  match t with
  | LLeaf => t'
  | LBin n t1 t2 => LBin n (graft t1 t') (graft t2 t')
  end.

Lemma graft_unfold1  {A: Type} : forall t': LTree A,
    graft LLeaf  t' = t'.
Proof.
 intros t'; LTree_unfold (graft LLeaf t');
  case t'; simpl; auto.
Qed.

Lemma graft_unfold2 {A: Type}: forall (a:A) (t1 t2 t':LTree A),
                      (graft (LBin a t1 t2) t')=
                      (LBin a (graft t1 t') (graft t2 t')).
Proof.
 intros  a t1 t2 t'; LTree_unfold (graft (LBin a t1 t2) t'); simpl; auto.
Qed.


Lemma graft_unfold {A: Type}: forall  (t t': LTree A),
                     graft t t' = match t  with
                                  | LLeaf => t'
                                  | LBin n t1 t2 =>
                                             LBin  n (graft t1 t')
                                                     (graft t2 t')
                                  end.
Proof.
 intros  t t'; case t.
 - apply graft_unfold1. 
 - intros; apply graft_unfold2.
Qed.




