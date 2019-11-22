(** Examples with Standard Library's vectors  *)
(** 
 

Keywords : vectors, dependent types, dependent elimination *)

Require Import Bool Arith Vector.
Import VectorNotations.

Arguments cons {A} _ {n}  _ .
Arguments nil {A}.

(** A known problem ... *)

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
Admitted.

(** Plesae define a "cast" of the following type *)


Definition cast {A:Type}{n:nat}(v : t A n) : forall n', n = n' -> t A n'.
Admitted. (* replace with "Defined" *)

(** cast's is correct (w.r.t equiv) *)


Lemma equiv_cast : forall (A:Type) n (v : t A n) n' (e: n = n'),
    v == cast v n' e.
Proof.
Admitted.

(** equivalence is (almost) equality *)

Lemma equiv_eq {A : Type}  : forall n (v w : t A n),
     v == w -> v = w.
Proof.
Admitted.


Lemma cast_eq {A} {n p} (v : t A n) (w : t A p) (e : n = p):
   v == w -> w = cast v p e.
Proof.
Admitted.


(** What is the problem with the following definition ? *)

Definition add_r {A} n a (v : t A n) : t A (S n) :=
  cast (v ++ [a]) _ (Nat.add_1_r n).

Compute add_r _ 7 [1;2;3].

(** Please give an alternate definition of add_r which has a correct behaviour
   (see below) *)

(*

About add_r'.

add_r' : forall (A : Type) (n : nat), A -> t A n -> t A (S n)

Argument A is implicit and maximally inserted
Argument scopes are [type_scope nat_scope _ _]
add_r' is transparent
                                                    

Compute add_r' _ 7 [1;2;3].

  = [1; 2; 3; 7]
     : t nat 4

*)
