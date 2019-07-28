Require Import Vector.

(** Solution CPDT like *)
Definition vhd' {A:Type}{n:nat}(v : t A n) :=
 match v in t _ n return (match n with 0 => unit | S _ => A end)
 with nil _ => tt
    | cons _  a _ _ => a
 end.

Lemma absurd_positive : ~ 0<> 0.
Proof.
  destruct 1;trivial.
Qed.

Definition vhd'' {A:Type}{n:nat}(v : t A n) : n <> 0 -> A :=
match v in t _ n return (n <> 0 -> A) with
| nil _ => (fun h : 0<> 0 => False_rect A (absurd_positive h))
| cons _ a _ w => fun h => a
end.

Definition vhead  {A:Type}{n:nat}(v : t A (S n)) : A.
apply (vhd'' (n:= S n) v); discriminate.
Defined.

Compute vhead (cons nat 42 _ (nil nat)).

Definition vtl'' {A:Type}{n:nat}(v : t A n) : match n with 0 => t A 0
                                                         | S p => t A p
                                                      end :=
match v in t _ n return  match n with 0 => t A 0
                                   | S p => t A p
                         end 
 with
| nil _ => nil _
| cons _ a _ w => w
end.


Definition vtail {A:Type}{n:nat}(v : t A (S n)) :  t A n
:= vtl'' v.

Compute vtail (cons nat 42 _ (nil nat)).


                                           
Definition vtl' {A:Type}{n:nat}(v : t A n) :=
 match v in t _ n return (match n with 0 => unit | S p => t A p end)
 with nil _ => tt
    | cons _  a _ w => w
 end.

Definition vtl {A}{n:nat}(v : t A (S n)) : t A n := vtl' v.


Definition vhd {A:Type}{n:nat}(v : t A (S n)) : A :=
 vhd' v.




Compute vhd (cons _ 4 _ (cons _ 6 _ (nil _))).


Definition v_id {A:Type}{n:nat} : t A n -> t A n.
 destruct n;intro v.
 exact (nil A).
 exact (cons _ (vhd v) _ (vtl v)).
Defined. 

Lemma v_id_eq {A:Type}{n:nat}:forall v: t A n, v = v_id v.
destruct v.
 reflexivity.
 reflexivity.
Qed.

Lemma zero_length_eq {A} : forall v : t A 0, v = nil A.
Proof.
 intro v.
 change (nil A) with (v_id v).
 apply v_id_eq.
Qed.

Lemma S_length_eq {A} {n:nat} : forall v : t A (S n), v = cons A (vhd v) n (vtl v).
Proof.
 intro v; change (cons A (vhd v) n (vtl v)) with (v_id v).
 apply v_id_eq.
Qed.

