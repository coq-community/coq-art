Definition sig_extract {A:Type}{P:A -> Prop} (x:sig P) : A :=
  match x with
  | exist _ a Ha => a
  end.

Theorem sig_extract_ok {A:Type}{P:A -> Prop} :
 forall y:sig P, P (sig_extract y).
Proof.
 now destruct y. 
Qed.

Require Import ZArith.
Open Scope Z_scope.

Parameter
  div_pair :
    forall a b:Z,
      0 < b ->
      {p : Z * Z | a = fst p * b + snd p  /\ 0 <= snd p < b}.

Definition div_pair' : forall a b:Z, 0 < b -> Z * Z :=
fun a b Hb => sig_extract (div_pair a b Hb).


Theorem div_pair'_ok :
 forall (a b:Z) (H:0 < b),
   let p := div_pair' a b H in
   a = fst p * b + snd p /\ 0 <= snd p < b.
Proof.
 intros a b H; pattern (div_pair' a b H);
  apply sig_extract_ok.
Qed.

