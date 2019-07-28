Require Import Arith.

Record RatPlus : Set := mkRat
  {top : nat; bottom : nat; bottom_condition : bottom <> 0}.

Axiom
  eq_RatPlus :
    forall r r':RatPlus, top r * bottom r' = top r' * bottom r -> r = r'.


Definition r0 : RatPlus.
Proof.
 refine (mkRat 4 6 _);  discriminate.  
Defined.

Definition r1 : RatPlus. 
Proof.   
 refine (mkRat 2 3 _); discriminate.
Defined.

Lemma r0_eq_r1 : r0 = r1.
Proof.
 apply eq_RatPlus; auto.
Qed.

Lemma axioms_are_risky : False.
Proof.
 absurd (r0 = r1);[discriminate | apply r0_eq_r1].
Qed.



