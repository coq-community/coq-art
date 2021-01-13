Require Import  month.

(** explicit use of month_rect

*)
Definition is_January_clumsy : month -> Prop :=
 month_rect (fun m => Prop) 
  True
  False
  False
  False
  False
  False
  False 
  False
  False
  False
  False
  False.
 
(** Tests: 


Compute is_January_clumsy February.

Compute is_January_clumsy January.
*)


(* alternate solution *)

  
Definition is_January (m : month) : Prop :=
 match m with
 | January => True 
 | _ => False
 end.

Remark both_versions_are_convertible : 
    is_January = is_January_clumsy.
Proof. reflexivity. Qed.
