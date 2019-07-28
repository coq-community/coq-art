Require Import Omega.
Require Import Wf_nat.

Definition f1_aux :
  forall x, (forall z, z < x ->{y:nat | z=0 \/ y < z})->{y:nat | x=0\/ y< x}.
 intros x; case x.
(* value for 0 *)
 intros rec; exists 0; auto.
 intros x'; case x'.
(* value for 1 *)
 intros rec; exists 0; auto.  
(* value for x > 1 *)
 refine
    (fun x'' rec => 
      match rec (S x'') _ with
      | (exist _ v H) =>
        match rec (S v) _ with
        | (exist _ v' H') => (exist _ (S v') _)
        end
      end); omega.
Defined.

Definition f1' : forall x, {y:nat | x=0 \/ y<x} :=
 (well_founded_induction lt_wf
   (fun x:nat => {y:nat | x=0\/ y<x})
   f1_aux).

Definition f1 (x:nat): nat :=
 match f1' x with (exist _ v _) => v end.
