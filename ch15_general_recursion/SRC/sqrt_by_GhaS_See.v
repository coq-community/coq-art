Require Import ZArith Lia.

(**  contributed by GhasSee 

  This version solves some computing issues 
    (computation of [sqrt' n]) 
*)

(** Euclidean division specification *) 

Definition div_type'' m n q r := m = q*n+r /\ r < n. 

Definition div_type  (m:nat)  :=
  forall n, 0 < n -> {q & { r | m = q*n+r /\ r < n }}.

Definition div_type' m n q    := { r | m = q*n+r /\ r < n }.

(* implementation by well-founded recursion *)

Definition div_F : 
  forall x, (forall y, y < x -> div_type y) -> div_type x. 
Proof. 
  unfold div_type at 2. 
  refine (fun m div_rec n Hlt => 
      match le_gt_dec n m with 
      | left H_n_le_m => 
          match div_rec (m-n) _ n _ with 
          | existT _ q (exist _ r H_spec) => 
              existT (div_type' m n) (S q)
                (exist (div_type'' m n (S q)) r _ )
          end 
      | right H_n_gt_m => 
            existT (div_type' m n) O (exist (div_type'' m n O) m _ ) end );  
  unfold div_type'' ; lia. 
Defined.  

Definition div :
  forall m n, 0 < n ->
              {q & {r | m = q*n+r /\ r < n }} :=
  well_founded_induction lt_wf div_type div_F.

Compute  match div 100 15 _
         with 
         | existT _ q (exist _ r _ )   => (q,r)
         end . 


(*   square root spec *)

Definition sqrt_type (n:nat)  :=
  {s & { r | n = s*s+r /\ n < S s * S s }}. 

Definition sqrt_type' n s := { r | n = s*s+r /\ n < (S s)*(S s) }.

Definition sqrt_type'' n s r  := n = s*s+r /\ n < (S s)*(S s).  


Definition sqrt_F : 
  forall x, (forall y, y < x -> sqrt_type y) -> sqrt_type x. 
Proof. 
  destruct x. 
  - refine (fun sqrt_rec => existT _ 0 (exist _ 0 _ )); lia. 
  - unfold sqrt_type at 2. 
    refine (fun sqrt_rec => 
      let n := S x in 
      match div n 4 _ with 
      | existT _ q (exist _ r0 _ ) => 
          match sqrt_rec q _ with 
          | existT _ s' (exist _ r' H_spec) => 
              match le_gt_dec (S(4*s')) (4*r'+r0) with 
              | left HSs => 
                  let s := S(2*s') in 
                  let r := 4*r'+r0 - S(4*s') in 
                  existT(sqrt_type' n) s
                    (exist (sqrt_type'' n s) r _ ) 
              | right Hs => 
                  let s := 2*s' in 
                  let r := 4*r'+r0 in 
                  existT(sqrt_type' n) s
                    (exist (sqrt_type'' n s) r _ )  end end end); 
    unfold sqrt_type''; auto with zarith. 
Defined. 

Definition sqrt : forall n, sqrt_type n :=
  well_founded_induction lt_wf sqrt_type sqrt_F. 

Compute match sqrt 10 with | existT _ s _ => s end . 



(* ex. 15.11 *) 
Definition sqrt_F' : 
  forall x, (forall y, y < x -> sqrt_type y) -> sqrt_type x. 
Proof. 
  destruct x. 
  - intros. exists 0. exists 0. auto with arith.  
  - intros sqrt_rec. set (S x) as n. fold n. 
    refine (match div n 4 _ with 
            | existT _ q (exist _ r0 _) => _ end );
      auto with zarith. 
    + destruct (sqrt_rec q) as [s' [r' [H1' H2']]];
        auto with zarith.  
      * { destruct (le_gt_dec (S(4*s')) (4*r'+r0)).   
          - exists (S(2*s')); exists (4*r'+r0-S(4*s'));
              auto with zarith.            
        - exists (2*s'), (4*r'+r0); auto with zarith. }
Defined.  

Definition sqrt' : forall n:nat, sqrt_type n :=
  well_founded_induction lt_wf sqrt_type sqrt_F'. 

(* hurrah !!! *)

Compute match sqrt' 42 with existT _ s _ => s end. 

