Lemma all_perm :
 forall (A:Type) (P:A -> A -> Prop),
   (forall x y:A, P x y) -> forall x y:A, P y x.
Proof.  auto. Qed.


Lemma resolution :
 forall (A:Type) (P Q R S: A -> Prop),
   (forall a:A, Q a -> R a -> S a) ->
   (forall b:A, P b -> Q b) -> 
   forall c:A, P c -> R c -> S c.
Proof.  auto. Qed.




