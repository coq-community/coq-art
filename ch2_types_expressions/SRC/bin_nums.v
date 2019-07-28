Require Export NArith.
Open Scope N_scope.

Definition pos_log2 (p:positive) : N :=
N.log2 (Npos p).

(** Write a function that given any positive number p, returns a pair
   of type (n, q) : N * positive such that p = 2^n * q

*)

Fixpoint decompose2 (p:positive) : N * positive :=
match p with xH => (0,xH)
           | xI q => (0, p)
           | xO q => let d := decompose2 q in (fst d + 1, snd d)
end.

Compute decompose2 (88%positive).
Compute decompose2 (1024%positive).

(** binary exponentiation *)

Definition sqr_pos (p:positive) := (p * p)%positive.

Fixpoint binary_pow_aux (x:N)(a:N)(p:positive) : N :=
 match p with xH => a * x
            | xO q  => binary_pow_aux (x * x) a q
            | xI q  => binary_pow_aux (x * x)  (a * x ) q

end.

Definition pow  (x:N) (n : N) :=
  match n with 0 => 1
             | Npos 1 => x
             | Npos p => binary_pow_aux x x (Pos.pred p)
 end.

Compute pow 2 5.
Compute pow 2 10.



(** Comparison with N.pow *)

Time Compute 1 ^ 55556666.

Time Compute pow 1 55556666.

Definition pow_test (x n:N) :=
  N.eqb (pow x n) (N.pow x n).

Compute pow_test 2  555.


Fixpoint exp2_pos  (p:positive) : positive :=
(match p with 1 => 2
           | p~0 => sqr_pos (exp2_pos p)
           | p~1 => (sqr_pos (exp2_pos p))~0
 end)%positive.


Definition exp2 (n:N) : positive :=
match n with N0 => xH
           | Npos p =>  (exp2_pos p)
end.


Compute exp2 10.

Compute exp2 7.



Compute pos_log2 63%positive.
Compute pos_log2 1023%positive.


Definition test_exp2 (p:positive) := N.eqb (Npos p)  (pos_log2 (exp2 (Npos p))).
Compute test_exp2 45%positive.


