Require Export ZArith.
Require Export Zwf.
Require Export Zcompare.
Check Zwf.
Check Zwf_well_founded.
Open Scope Z_scope.
 
Definition factZ_F: forall (x : Z), (forall y, Zwf 0 y x ->  Z) ->  Z.
refine (fun x fact =>
           match Z_lt_le_dec x 0 with
             left _ => 0
            | right Hle =>
                match Z.eq_dec x 0 with
                  left _ => 1
                 | right Hne => x * fact (x - 1) _
                end
           end).
unfold Zwf; omega.
Qed.
