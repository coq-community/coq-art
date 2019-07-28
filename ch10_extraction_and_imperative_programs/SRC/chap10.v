Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export Omega.
Require Export Zwf.
Require Export Inverse_Image Extraction.


Open Scope nat_scope.


Extraction "pplus" Pplus.


Fixpoint Psucc (x:positive) : positive :=
  match x with
    xI x' => xO (Psucc x') | xO x' => xI x' | xH => xO xH
  end.


Fixpoint nth' (A:Set)(l:list A)(n:nat){struct n} : option A :=
  match l, n with
  |  nil, _ => None
  | cons a tl, O => Some a
  | cons a tl, S p => nth' A tl p
  end.


Parameters 
 (xH_xI : forall p:positive, xH<>xI p)
 (xH_xO : forall p:positive, xH<>xO p)
 (eq_xI : forall p q:positive, p=q-> xI p = xI q)
 (eq_xO : forall p q:positive, p=q-> xO p = xO q)
 (not_eq_xI : forall p q:positive, p<>q-> xI p <> xI q)
 (not_eq_xO : forall p q:positive, p<>q-> xO p <> xO q)
 (xI_xO : forall p q:positive, xI p<>xO q).

Fixpoint eq_positive_dec (n m:positive){struct m} :
   {n = m}+{n <> m} :=
  match n return {n = m}+{n <> m} with
  | xI p =>
    match m return {xI p = m}+{xI p <> m} with
    | xI q =>
      match eq_positive_dec p q with
      | left heq => left _ (eq_xI p q heq)
      | right hneq => right _ (not_eq_xI p q hneq)
      end
    | xO q => right _ (xI_xO p q)
    | xH => right _ (sym_not_equal (xH_xI p))
    end
  | xO p =>
    match m return {xO p = m}+{xO p <> m} with
    | xI q => right _ (sym_not_equal (xI_xO q p))
    | xO q =>
      match eq_positive_dec p q with
      | left heq => left _ (eq_xO p q heq)
      | right hneq => right _ (not_eq_xO p q hneq)
      end
    | xH => right _ (sym_not_equal (xH_xO p))
    end
  | xH => match m return {xH = m}+{xH <> m} with
                   | xI q => right _ (xH_xI q)
                   | xO q => right _ (xH_xO q)
                   | xH => left _ (refl_equal xH)
                   end
  end.

Definition pred' (n:nat) : n <> 0 -> nat :=
  match n return n <> 0 -> nat with
  | O => fun h:0 <> 0 => False_rec nat (h (refl_equal 0))
  | S p => fun h:S p <> 0 => p
  end.

Definition pred2 (n:nat) : nat :=
  match eq_nat_dec n 0 with
  | left h => 0
  | right h' => pred' n h'
  end.

Definition pred'_on_O := pred' O.

(* the following module is just here for understanding
   what is already built in Coq's libraries *)

Module redefine_acc. 

Inductive Acc {A:Type}(R:A->A->Prop) : A->Prop :=
    Acc_intro : forall x:A, (forall y:A, R y x -> Acc  R y) ->
                             Acc  R x.

Arguments Acc_intro {A R} x f.

Definition Acc_inv {A:Type}(R:A->A->Prop)(x:A)(Hacc:Acc  R x) :
  forall y:A, R y x -> Acc  R y :=
  match Hacc as H in (Acc  _ x)
        return (forall y:A, R y x -> Acc  R y) with
  | Acc_intro  x f => f
  end.

Fixpoint Acc_iter {A:Type}(R:A->A->Prop)(P:A->Type)
 (f:forall x:A, (forall y:A, R y x -> P y)-> P x)(x:A)
 (hacc:Acc  R x){struct hacc} : P x :=
  f x (fun (y:A)(hy:R y x) =>
       Acc_iter  R P f y (Acc_inv  R x hacc y hy)).

Definition well_founded_induction {A:Type}(R:A->A->Prop)
  (Rwf:forall x:A, Acc  R x)(P:A->Type)
  (F:forall x:A, (forall y:A, R y x -> P y)-> P x)(x:A) : P x :=
  Acc_iter  R P F x (Rwf x). 

End redefine_acc.

Fixpoint div2 (n:nat) : nat :=
  match n with S (S p) => S (div2 p) | _ => 0 end.

Parameters 
  (div2_lt : forall x:nat, div2 (S x) < S x)
  (lt_wf : forall x:nat, Acc lt x).

Definition log2_aux_F (x:nat) : (forall y:nat, y < x -> nat)->nat :=
  match x return (forall y:nat, y < x -> nat)-> nat with
  | O => fun _ => 0
  | S p => fun f => S (f (div2 (S p))(div2_lt p))
  end.

Definition log2_aux :=
  well_founded_induction lt_wf (fun _:nat => nat) log2_aux_F.

Definition log2 (x:nat)(h:x <> 0) : nat := log2_aux (pred x).

Definition sumbool_to_or (A B:Prop)(v:{A}+{B}) : A\/B :=
  match v with
  | left Ha => or_introl B Ha
  | right Hb => or_intror A Hb
  end.

Open Scope Z_scope. 

Record tuple : Set := mk_tuple {b:bool; x:Z}.


Definition Zgt_bool' :
  forall x y:Z, {Zgt_bool x y = true}+{Zgt_bool x y = false}.
 intros x0 y0; case (Zgt_bool x0 y0); auto.
Defined.


Definition loop1' :
  forall t:tuple, (forall t1:tuple, Zwf 0 (x t1)(x t) -> tuple)->tuple.
 refine
  (fun (t:tuple)
     (loop_again:forall t':tuple, Zwf 0 (x t')(x t) -> tuple) =>
     match Zgt_bool' (x t) 0 with
     | left h => loop_again (mk_tuple (b t)((x t)-1)) _
     | right h => t
     end).
 generalize (Zgt_cases (x t) 0); rewrite h; intros; cbn.
 unfold Zwf; omega.
Defined.

Definition loop1 : tuple->tuple :=
  well_founded_induction
    (wf_inverse_image tuple Z (Zwf 0) x (Zwf_well_founded 0))
    (fun _:tuple => tuple) loop1'.

Set Implicit Arguments.

Parameter array : Z->Set->Set.
Parameter new : forall (n:Z)(T:Set), T->array n T.
Parameter access : forall (n:Z)(T:Set), array n T -> Z->T.
Parameter
  store : forall (n:Z)(T:Set), array n T -> Z -> T -> array n T.

Axiom new_def :
    forall (n:Z)(T:Set)(v0:T)(i:Z),
      0 <= i < n -> access (new n v0) i = v0.

Axiom store_def_1 :
    forall (n:Z)(T:Set)(t:array n T)(v:T)(i:Z),
      0 <= i < n -> access (store t i v) i = v.

Axiom store_def_2 :
    forall (n:Z)(T:Set)(t:array n T)(v:T)(i j:Z),
    0 <= i < n -> 0 <= j < n -> i <> j ->
    access (store t i v) j = access t j.
Unset Implicit Arguments.

Parameter l : Z.

Record tuple':Set := mk_tuple' {a:array l Z; y:Z; z:Z}.

Definition insert_loop : tuple'->tuple'.
refine
 (well_founded_induction
    (wf_inverse_image _ _ _ (fun t:tuple' => l-(z t))
       (Zwf_well_founded 0))
    (fun _:tuple' => tuple')
    (fun (t:tuple')
       (loop_again:forall t':tuple',
                     Zwf 0 (l-(z t'))(l-(z t))->tuple') =>
       match Z_gt_le_dec l (z t) with
       | left h0 =>
         match Z_gt_le_dec (y t)(z t) with
         | left _ =>
             (fun (h1:0 <= (z t)-1 < l)
                (h2:0 <= (z t) < l) =>
                loop_again
                  (mk_tuple'
                     (store (a t)((z t)-1)
                            (access (a t)(z t)))
                     (y t)((z t)+1)) _) _ _
         | right _ =>
             (fun h1:0 <= (z t) < l =>
                loop_again
                  (mk_tuple' (store (a t)((z t)-1)(y t))
                      (y t) l)
                  _) _
         end
       | right h3 => t
       end)). 
 Abort.

 Check (forall t:tuple', 0 < (z t) -> tuple').
 Definition insert_loop' : forall t:tuple', 0 < (z t) -> tuple'.
  refine
  (well_founded_induction
    (wf_inverse_image _ _ _ 
       (fun t:tuple' => l-(z t))(Zwf_well_founded 0))
    (fun t:tuple' => 0 < (z t) -> tuple')
    (fun (t:tuple')
       (loop_again:forall t':tuple',
                     Zwf 0 (l-(z t'))(l-(z t)) ->
                     0 < (z t') -> tuple')(h4:0 < (z t)) =>
       match Z_gt_le_dec l (z t) with
       | left h0 =>
         match Z_gt_le_dec (y t)(z t) with
         | left _ =>
             (fun (h1:0 <= (z t)-1 < l)
                (h2:0 <= (z t) < l) =>
                loop_again
                  (mk_tuple'
                     (store (a t)((z t)-1)(access (a t)(z t)))
                     (y t)((z t)+1)) _ _) _ _
         | right _ =>
             (fun h1:0 <= (z t) < l =>
                loop_again
                  (mk_tuple' (store (a t)((z t)-1)(y t))(y t) l)
                  _ _) _
         end
       | right _ => t
       end)); cbn; try (unfold Zwf); omega. 
Defined.
