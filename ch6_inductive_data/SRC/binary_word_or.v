Require Export Bool.

Inductive binary_word : nat -> Set :=
| bw0 :  binary_word 0
| bwS (p : nat)(b:bool)(w: binary_word p) : binary_word (S p).


Lemma discriminate_O_S {p:nat}:  0 = S p -> False.
Proof.
 intros;discriminate.
Qed.

Lemma  discriminate_S_O {p:nat}:  S p = 0 -> False.
Proof.
 intros;discriminate.
Qed.


Fixpoint binary_word_or (n:nat)(w1:binary_word n) {struct w1}:
    binary_word n -> binary_word n :=
 match w1 in binary_word p return binary_word p -> binary_word p with
   bw0 =>
     (fun w2:binary_word 0 =>
        match w2 in binary_word p' return p'=0->binary_word p' with
          bw0 =>
            (fun h => bw0)
        | bwS q b w2' =>
            (fun h => False_rec (binary_word (S q)) (discriminate_S_O h))
        end (refl_equal 0))
  | bwS q b1 w1' =>
      (fun w2:binary_word (S q) =>
        match w2 in binary_word p' return S q=p'->binary_word p' with
          bw0 =>
            (fun h => False_rec (binary_word 0) (discriminate_S_O h))
        | bwS q' b2 w2' =>
            (fun h =>
               bwS q'
                  (orb b1 b2)
                  (binary_word_or q'
(* this use of eq_rec transforms w1' into an element of (binary_word (S q'))
    instead of (binary_word (S q)), thanks to the equality h. *)
                    (eq_rec (S q)
                      (fun v:nat => binary_word (pred v))
                      w1'
                      (S q')
                      (h:S q=S q'))
                      w2'))
         end (refl_equal (S q)))
  end.

Lemma binary_or_idempotent (n:nat) : forall w: binary_word n,
  binary_word_or n w w = w.
Proof. 
induction w as [ | n b w IHw].
- simpl;auto.
- simpl;rewrite IHw; now destruct b.
Qed.

