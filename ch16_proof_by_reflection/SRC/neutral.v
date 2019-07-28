Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export Omega.
Require Export Zwf.
Require Export Relations.
Require Export Inverse_Image.
Require Export Transitive_Closure.
Require Export Zdiv.
 
Open Scope nat_scope.

(* we need to add an object in the abstract tree structure to
   represent the neutral element. *)
 
Inductive bin : Set :=
 | node: bin -> bin ->  bin
 | leaf: nat ->  bin
 | neutral: bin .

(* flattening is unchanged. *)
 
Fixpoint flatten_aux (t fin : bin) {struct t} : bin :=
 match t with
  | node t1 t2 => flatten_aux t1 (flatten_aux t2 fin)
  | x => node x fin
 end.
 
Fixpoint flatten (t : bin) : bin :=
 match t with node t1 t2 => flatten_aux t1 (flatten t2) | x => x end.

(* Here is a function that removes the neutral elements from a flat tree
   This needs to be done in two steps because of the right-most subtree.*)
 
Fixpoint remove_neutral1 (t : bin) : bin :=
 match t with
   leaf n => leaf n
  | neutral => neutral
  | node neutral t' => remove_neutral1 t'
  | node t t' => node t (remove_neutral1 t')
 end.
 
Fixpoint remove_neutral2 (t : bin) : bin :=
 match t with
   leaf n => leaf n
  | neutral => neutral
  | node t neutral => t
  | node t1 t2 => node t1 (remove_neutral2 t2)
 end.
 
Definition remove_neutral (t : bin) := remove_neutral2 (remove_neutral1 t).
 
Section assoc_eq.
Variables
   (A : Set) (f : A -> A ->  A) (zero_A : A)
   (assoc : forall (x y z : A),  f x (f y z) = f (f x y) z)
   (zero_left : forall (x : A),  f zero_A x = x)
   (zero_right : forall (x : A),  f x zero_A = x).
 
(* The function bin_A can now be simplified. the neutral element will be used
   as the default value for nth. *)
Fixpoint bin_A (l : list A) (t : bin) {struct t} : A :=
 match t with
   node t1 t2 => f (bin_A l t1) (bin_A l t2)
  | leaf n => nth n l zero_A
  | neutral => zero_A
 end.
 
(* all theorems are simplified accordingly. *)

Theorem flatten_aux_valid_A:
 forall (l : list A) (t t' : bin),
  f (bin_A l t) (bin_A l t') = bin_A l (flatten_aux t t').
Proof.
intros l t; elim t; simpl; auto.
intros t1 IHt1 t2 IHt2 t'; rewrite <- IHt1; rewrite <- IHt2.
symmetry; apply assoc.
Qed.
 
Theorem flatten_valid_A:
 forall (l : list A) (t : bin),  bin_A l t = bin_A l (flatten t).
Proof.
intros l t; elim t; simpl; trivial.
intros t1 IHt1 t2 IHt2; rewrite <- flatten_aux_valid_A; now rewrite <- IHt2.
Qed.
 
Theorem flatten_valid_A_2:
 forall (t t' : bin) (l : list A),
 bin_A l (flatten t) = bin_A l (flatten t') ->  bin_A l t = bin_A l t'.
Proof.
intros t t' l Heq.
rewrite (flatten_valid_A l t); now rewrite (flatten_valid_A l t').
Qed.
 
Theorem remove_neutral1_valid_A:
 forall (l : list A) (t : bin),  bin_A l (remove_neutral1 t) = bin_A l t.
Proof.
intros l t; elim t; auto.
intros t1; case t1; simpl.
- intros t1' t1'' IHt1 t2 IHt2; rewrite IHt2; trivial.
- intros n IHt1 t2 IHt2; rewrite IHt2; trivial.
- intros IHt1 t2 IHt2; rewrite zero_left; trivial.
Qed.
 
Theorem remove_neutral2_valid_A:
 forall (l : list A) (t : bin),  bin_A l (remove_neutral2 t) = bin_A l t.
Proof.
intros l t; elim t; auto.
intros t1 IHt1 t2; case t2; simpl.
- intros t2' t2'' IHt2; rewrite IHt2; trivial.
- auto.
- intros IHt2; rewrite zero_right; trivial.
Qed.
 
Theorem remove_neutral_equal:
 forall (t t' : bin) (l : list A),
 bin_A l (remove_neutral t) = bin_A l (remove_neutral t') ->
  bin_A l t = bin_A l t'.
Proof.
unfold remove_neutral; intros t t' l.
repeat rewrite remove_neutral2_valid_A.
repeat rewrite remove_neutral1_valid_A.
trivial.
Qed.
 
End assoc_eq.
 
Ltac term_list f l zero v := match v with
                              | f ?X1 ?X2 => let l1 := term_list f l zero X2 in
                                             term_list f l1 zero X1
                              | zero => l
                              | ?X1 => constr:(cons X1 l) end.
 
Ltac compute_rank l n v := match l with
                       | cons ?X1 ?X2 =>
                         let tl := constr:(X2) in
                           match constr:(X1 = v) with
                           | ?X1 = ?X1 => n
                           | _ => compute_rank tl (S n) v
                            end
                       end.
 
Ltac
model_aux l f zero v := match v with
                         | f ?X1 ?X2 => let r1 := model_aux l f zero X1 with
                                            r2 := model_aux l f zero X2 in
                                        constr:(node r1 r2)
                         | zero => constr:(neutral)
                         | ?X1 => let n := compute_rank l 0 X1 in
                                  constr:(leaf n)
                         end.
 
Ltac model_A A f zero v := let l := term_list f (nil (A:=A)) zero v in
                           let t := model_aux l f zero v in
                           constr:(bin_A A f zero l t).
 
(* At the end of the tactic, we also remove the zero. *)
Ltac assoc_eq A f zero assoc_thm neutral_left_thm neutral_right_thm :=
match goal with
| |- @eq A ?X1 ?X2 =>
let term1 := model_A A f zero X1 with
    term2 := model_A A f zero X2 in
(change (term1 = term2); apply flatten_valid_A_2 with ( 1 := assoc_thm );
  apply remove_neutral_equal
       with ( 1 := neutral_left_thm ) ( 2 := neutral_right_thm ); auto) end.
 
Theorem reflection_test3:
 forall (x y z t u : Z),  (x * (((y * z) *1 )* (t * u)) = (x * (1 * y)) * (z * (t * u)) * 1)%Z.
Proof.
intros; assoc_eq Z Zmult 1%Z Zmult_assoc Zmult_1_l Zmult_1_r.
Qed.


