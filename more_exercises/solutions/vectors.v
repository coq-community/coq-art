(** Examples with Standard library's vectors  *)
(** 
 

Keywords : vectors, dependent types, dependent elimination *)

Require Import Bool Arith Vector.
Import VectorNotations.
Arguments cons {A} _ {n}  _ .
Arguments nil {A}.

Fail
Lemma app_assoc {d e f:nat} {A: Type} :
  forall (u: t A d)( v : t A e) (w: t A f),
    (u ++ v) ++ w =  u ++ (v ++ w).

(* So, let us define an equivalence relation *)


Definition equiv {A} {n p : nat} (v: t A n) (w: t A p) :=
  to_list v = to_list w.

Infix "==" := equiv (at level 70) : type_scope.

Lemma app_assoc {d e f:nat} {A: Type} :
  forall (u: t A d)( v : t A e) (w: t A f),
    (u ++ v) ++ w ==  u ++ (v ++ w).
Proof.
  intros. 
  induction u; simpl.
  - reflexivity.
  - red.   cbn; f_equal. apply IHu. 
Qed.

Definition cast {A:Type}{n:nat}(v : t A n) : forall n', n = n' -> t A n'.
  induction v.
  - intros n' e.  subst n'. exact [].
  - intros n' e. destruct n'.
    + discriminate.
    + injection e; intros. exact (h :: IHv n' H).
Defined.


Lemma to_list_cons {A} (a:A) n (v: t A n) :
  to_list (cons a v) = List.cons a (to_list v).
Proof. reflexivity. Qed.


Lemma equiv_cast : forall (A:Type) n (v : t A n) n' (e: n = n'),
    v == cast v n' e.
Proof.
  induction v.
  - intros; now subst.
  - intros;  subst; simpl; red ; repeat rewrite to_list_cons.
    f_equal;  apply (IHv n).
Qed.


(* The decomposition lemma for vectors *)


Definition Vid {A:Type} n : t A n -> t A n :=
  match n with
    0 => fun w => []
  | S p => fun w =>  hd w :: tl w
  end.

Lemma Vid_eq : forall (n:nat) (A:Type)(v:t A n), v = Vid n v.
Proof.
 destruct v; reflexivity.
Defined.


Definition  decomp0 (A:Type) (v:t A 0) : v = nil :=
  Vid_eq 0 A v.


Theorem decompS :
  forall (A : Type) (n : nat) (v : t A (S n)),
  v = cons (hd v) (tl v).
Proof.
 intros.
  now   rewrite (Vid_eq (S n) A v).
Defined.


Definition vector_double_rect : 
    forall (A:Type) (X: forall (n:nat), t A n -> t A n -> Type),
        X 0 nil nil ->
        (forall n (v1 v2 : t A n) a b, X n v1 v2 ->
             X (S n) (cons a v1) (cons  b v2)) ->
        forall n (v1 v2 : t A n), X n v1 v2.
 induction n.
 - intros; rewrite (decomp0 _ v1); rewrite (decomp0 _ v2); auto.
 - intros v1 v2; rewrite (decompS _ _ v1);rewrite (decompS _ _ v2);
     auto.
Defined.

Lemma equiv_eq {A : Type}  : forall n (v w : t A n),
     v == w -> v = w.
Proof.
  intros n v w.
  pattern n, v, w;  apply vector_double_rect.
  - reflexivity.    
  -  intros n0 v1 v2 a b H H0;    red in H0.
    repeat  rewrite to_list_cons in H0.
    injection H0.
    intros; subst b.
    f_equal; auto.
Qed.

Lemma cast_eq {A} {n p} (v : t A n) (w : t A p) (e : n = p):
   v == w -> w = cast v p e.
Proof.
  intros.
  apply equiv_eq.
  subst p.
  red.
  transitivity (to_list v); auto.
  apply equiv_cast.
Qed.


(** What is the problem with the following definition ? *)

Definition add_r {A} n a (v : t A n) : t A (S n) :=
  cast (v ++ [a]) _ (Nat.add_1_r n).

Compute add_r _ 7 [1;2;3].

(** Please give an alternate definition of add_r *)

Definition add_1_r_transparent n : n+1 = S n.
induction n; simpl; auto.
Defined.

Definition add_r' {A} n a (v : t A n) : t A (S n) :=
  cast (v ++ [a]) _ (add_1_r_transparent n).

Compute add_r' _ 7 [1;2;3].

(*
  = [1; 2; 3; 7]
     : t nat 4
*)


