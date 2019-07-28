Inductive binary_word : nat -> Set :=
  bw0 :  binary_word 0
| bwS : forall p:nat, bool -> binary_word p -> binary_word (S p).

Fixpoint binary_word_concat
   (n:nat)(w1:binary_word n)(m:nat)(w2:binary_word m) {struct w1} :
      binary_word (n+m) :=
 match w1 in binary_word p return binary_word (p+m) with
   bw0  => w2
 | bwS q b w1' =>
   bwS (q+m) b (binary_word_concat q w1' m w2)
 end.


Arguments bwS {p} _ _.
Arguments binary_word_concat {n} w1 {m} w2.

(** Tests:

Let bw := binary_word_concat (bwS true (bwS false bw0))
                             (bwS true (bwS false bw0)).

Print bw.


Check (bw : binary_word 4).
*)
