Require Import chap13.

Set Implicit Arguments.

CoFixpoint LMap (A B: Type)(f : A -> B) (u : LList A) : LList B :=
  match u with
   LNil => (LNil (A:=B))
  |LCons x u' => LCons (f x) (LMap  f u')
  end.

(* example *)

Definition cubes := LMap (fun x => x * x * x) (from 0).

(** Tests :
Eval simpl in (LList_decomp_n 5 cubes).

*)

(*

CoFixpoint LMapcan (A B: Set) (f : A -> LList B)(u : LList A) : LList B :=
   match u with
   LNil => (LNil (A:=B))
  |LCons x u' => LAppend (f x) (LMapcan  f u')
  end.
  

Recursive definition of LMapcan is ill-formed.
In environment
LMapcan : forall A B : Set, (A -> LList B) -> LList A -> LList B
A : Set
B : Set
f : A -> LList B
u : LList A
x : A
u' : LList A
unguarded recursive call in
(cofix LAppend (A : Set) (u v : LList A) : LList A :=
   match u with
   | LNil => v
   | LCons a u' => LCons a (LAppend A u' v)
   end)



Notice that, if such a LMapcan would be defineable, the evaluation of
the following term would loop ! :

LHead (LMapcan (fun n => match (Peano_dec.eq_nat_dec n (n+1))
                with left _ => (LCons 1 LNil)
                   | right _ => LNil (A:= nat)
                end)
               (from 0))

*)
