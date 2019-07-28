Require Export ZArith.
Require Export ZArithRing.

Open Scope Z_scope.

(* The following tactic looks for all the instances of
   "Zpos (xO p)" and "Zpos (xI p)" and replaces them with
   polynomial expressions in p, but avoids doing it for the numbers
   2 and 3 which are "Zpos (xO xH)" and "Zpos (xI xH)". *)

Ltac Zpos_x_tac :=
 match goal with
   |- context [Zpos (xO ?P)] =>
       match P with
        | xH => fail 1
        | ?X2 => rewrite (Zpos_xO X2); Zpos_x_tac
       end
 | |- context [Zpos (xI ?P)] =>
       match P with
        | xH => fail 1
        | ?X2 => rewrite (Zpos_xI X2); Zpos_x_tac
       end
 | |- _ => idtac
 end.

(* Here is an example using this tactic. *)

Theorem ex1 :
  forall p, Zpos (xO (xI p))=4*(Zpos p)+2.
Proof.
 intros p.
 Zpos_x_tac.
 rewrite Zmult_plus_distr_r; simpl (2*1).
 rewrite Zmult_assoc; reflexivity.
Qed.
