(* We consider the discrete plan the coordinate system of which 
    is based on Z *)
Require Import List  ZArith  Bool.
Open Scope Z_scope.
Require Import Relations  Setoid  Morphisms  RelationClasses.
Require Import EMonoid.



(** Types for representing routes in the dicrete  plane *)

Inductive direction : Type := North | East | South | West.
Definition route := list direction.

Record Point : Type :=
 {Point_x : Z;
  Point_y : Z}.

Definition Point_O := Build_Point 0 0.

Definition translate (dx dy:Z) (P : Point) :=
  Build_Point (Point_x P + dx) (Point_y P + dy).

(** Equality test  between Points *)

Definition Point_eqb (P P':Point) :=
   Zeq_bool (Point_x P) (Point_x P') &&
   Zeq_bool (Point_y P) (Point_y P').

(* Prove the correctness of Point_eqb *)

Lemma Point_eqb_correct : forall p p', Point_eqb p p' = true <->
                                       p = p'.
Proof.
 destruct p;destruct p';simpl;split.
 -  unfold Point_eqb; simpl; rewrite andb_true_iff; destruct 1.
    repeat rewrite <- Zeq_is_eq_bool in *.
    now  rewrite H, H0.
 -  injection 1;intros H0 H1;rewrite H0, H1; unfold Point_eqb; simpl;
    rewrite andb_true_iff;repeat rewrite <- Zeq_is_eq_bool; now split.
Qed.

(**  (move P r) follows the route r starting from P *)

Fixpoint move (r:route) (P:Point) : Point :=
 match r with
 | nil => P
 | North :: r' => move r' (translate 0 1 P)
 | East :: r' => move r' (translate 1 0 P) 
 | South :: r' => move r' (translate 0 (-1) P)
 | West :: r' => move r' (translate (-1) 0 P)
 end.

(**  We consider that two routes are "equivalent" if they define
  the same moves. For instance, the routes
  East::North::West::South::East::nil and East::nil are equivalent *)

Definition route_equiv : relation route :=
  fun r r' => forall P:Point , move r P = move  r' P.

Infix "=r=" := route_equiv (at level 70):type_scope.

Example Ex1 : East::North::West::South::East::nil =r= East::nil.
Proof.
 intro P;destruct P;simpl; unfold route_equiv, translate;simpl;f_equal; ring.
Qed.

Lemma route_equiv_refl : reflexive _ route_equiv.
Proof.  intros r p;reflexivity. Qed.

Lemma route_equiv_sym : symmetric _ route_equiv.
Proof.  intros r r' H p; symmetry;apply H. Qed.

Lemma route_equiv_trans : transitive _ route_equiv.
Proof.  intros r r' r'' H H' p; rewrite H; apply H'. Qed.

Instance route_equiv_Equiv : Equivalence  route_equiv.
Proof.
split;  [apply route_equiv_refl |  apply route_equiv_sym |  apply route_equiv_trans].
Qed.


(* Cons and app are Proper functions w.r.t. route_equiv *)

Lemma route_cons : forall r r' d, r =r= r' -> d::r =r= d::r'.
Proof. 
 intros r r' d H P;destruct d;simpl;rewrite H;reflexivity.
Qed.

Example Ex2 :  South::East::North::West::South::East::nil =r= South::East::nil.
Proof. apply route_cons;apply Ex1. Qed.


Instance cons_route_Proper (d:direction): 
    Proper (route_equiv ==> route_equiv) (cons d) .
Proof.
 intros r r' H ; now apply route_cons.
Qed.


(**  cons_route_Proper allows to replace a route with an =r= equivalent one
     in a context composed by "cons" *)

Example SW : forall r r', r =r= r' ->
                  South::West::r =r= South::West::r'.
Proof. 
 intros r r' H; now rewrite H.
Qed.


Instance move_Proper  : Proper (route_equiv ==> @eq Point ==> @eq Point) move . 
Proof.
 intros r r' Hr_r' p q Hpq; rewrite Hpq; apply Hr_r'.
Qed.

Example length_not_Proper : ~Proper (route_equiv ==> @eq nat) (@length _).
Proof.
 intro H; generalize (H (North::South::nil) nil);simpl;intro H0.
 discriminate H0.
 -  intro P;destruct P; simpl;unfold translate; simpl;f_equal;simpl;ring.
Qed.



Lemma route_compose : forall r r' P, move (r++r') P = move r' (move r P).
Proof.  
 induction r as [|d s IHs]; simpl;
 [auto | destruct d; intros;rewrite IHs;auto].
Qed.


Instance app_route_Proper : Proper (route_equiv==>route_equiv ==> route_equiv)
 (@app direction).
Proof.
 intros r r' H r'' r''' H' P.
 repeat rewrite route_compose; rewrite H, H';reflexivity.
Qed.


Example Ex3 : forall r, North::East::South::West::r =r= r.
Proof. 
 intros r P;destruct P;simpl; 
  unfold route_equiv, translate;simpl;do 2 f_equal;ring.
Qed.

Example Ex4 : forall r r', r =r= r' -> 
                North::East::South::West::r =r= r'.
Proof. intros r r' H. now rewrite Ex3. Qed.

Example Ex5 : forall r r',  r++ North::East::South::West::r' =r= r++r'.
Proof. intros r r'; now rewrite Ex3. Qed.


Lemma translate_comm : forall dx dy dx' dy' P,
    translate dx dy (translate dx' dy' P) =
    translate dx' dy' (translate dx dy P).
Proof.
  unfold translate; simpl; intros; f_equal; ring.
 Qed.

Lemma move_translate : forall r P dx dy , move r (translate dx dy P) =
                                                translate dx dy (move r P).
Proof.
 induction r as [|a r];simpl;[reflexivity|].  
 destruct a;simpl; intros;rewrite <- IHr;rewrite  (translate_comm );auto.
Qed.

Lemma move_comm : forall r r' P  , move r (move r' P)  =
                                   move r' (move r P) .
Proof.
induction r as [| a r'];[reflexivity|].
- simpl;destruct a;
 intros;repeat rewrite move_translate;rewrite IHr';auto.
Qed.

Lemma app_comm : forall r r', r++r' =r=  r'++r.
Proof.
 intros r r' P;repeat rewrite route_compose; apply move_comm.
Qed.

(** the following lemma  will be used for deciding route equivalence *)

Lemma route_equiv_Origin : forall r r', r =r= r' <->
                                        move r Point_O  = move r' Point_O .
Proof.
split;intro H.
- now rewrite H.
- intro P;replace P with (translate (Point_x P) (Point_y P) Point_O).
 +   repeat rewrite move_translate.
     rewrite H;reflexivity.
 + destruct P;simpl;unfold translate;f_equal.
Qed.

Definition route_eqb r r' : bool :=
   Point_eqb (move r Point_O) (move r' Point_O).

(**  ... we can now prove route_eqb's  correctness *)

Lemma route_equiv_equivb : forall r r', route_equiv r r' <->
                                        route_eqb r r' = true.
Proof.
 intros r r' ; rewrite route_equiv_Origin; 
 unfold route_eqb;rewrite Point_eqb_correct;tauto.
Qed.

Ltac route_eq_tac := rewrite route_equiv_equivb;reflexivity.

(** another proof of Ex1, using computation  *)

Example Ex1' : East::North::West::South::East::nil =r= East::nil.
Proof. route_eq_tac. Qed.

Lemma north_south_0 : forall r, North::South::r =r=  r.
Proof.
 intro r; change ((North::South::nil)++ r =r=  r).
 setoid_replace (North :: South :: nil) with  (@nil direction);
  [reflexivity |route_eq_tac ]. 
Qed.

Lemma north_south_simpl : forall r r', r++ North::South::r' =r=  r++r'.
Proof.
 induction r as [|a r'];simpl.
 -  intro r';rewrite north_south_0;reflexivity.  
 -  intros r1;now rewrite IHr' .
Qed.


(* we want to prove that, if some route contains two steps in opposite
   directions, then the route can be shortened *)

Definition opposite (d d':direction):= match d,d' with 
        | North,South => True
        | South, North => True
        | East, West => True
        | West, East => True
        | _, _ => False
end.


Inductive  Useless_steps_in (r:route) : Type :=
Useless_i: forall r0 r1 r2 d d1,  r = r0++(d::r1)++(d1::r2) ->
                                  opposite d d1 ->
                                  Useless_steps_in r.

Lemma opposite_cons : forall d d1 r, opposite d d1 -> d1::d::r =r= r.
Proof.
 intros d d1 r H;destruct d,d1;simpl ;try contradiction ;
 intro P;destruct P;simpl;auto; unfold translate;simpl; repeat f_equal;ring.
Qed.

Lemma cons2_comm : forall d d' r, d::d'::r =r= d'::d::r.
Proof.
 intros d d' r; change ((d::nil)++(d'::nil)++r =r= (d'::nil)++(d::nil)++r).
 do 2  rewrite <- app_ass.
 rewrite (app_comm  (d :: nil) (d'::nil));reflexivity.
Qed.


Lemma Useless_steps_shorter (r:route) :
  Useless_steps_in r -> {r' : route | r =r= r' /\ (length r' < length r)%nat}.
Proof.
 intro H;destruct H as [r0 r1 r2 d d1 H1 H2]. 
 exists (r0 ++ r1 ++ r2).
 split.
 -  subst r; replace (r0 ++ (d :: r1) ++ d1 :: r2) with
         (r0 ++ ((d::nil) ++ r1) ++ ((d1::nil)++r2))  by (simpl;auto).
     apply app_route_Proper;[reflexivity|].
     rewrite <- app_ass.
     apply app_route_Proper;[|reflexivity].
     transitivity ((d1::nil)++(d::r1)).
     rewrite app_comm; reflexivity.
      simpl;rewrite opposite_cons;[reflexivity|trivial].
 -  subst r; repeat (simpl;repeat  rewrite app_length); omega.
Qed.


(** Monoid structure on routes *)

Instance Route : EMonoid route_equiv (@app _)  nil .
Proof.
split.
- apply route_equiv_Equiv.
- apply app_route_Proper.
- intros x y z P;repeat rewrite  route_compose; trivial.
-  intros x  P;repeat rewrite  route_compose; trivial.
- intros x  P;repeat rewrite  route_compose; trivial.
Qed.

Example Ex6 : forall n, Epower (South::North::nil) n =r= nil.
Proof. 
 induction n as [| p IHp];simpl;[reflexivity|].
 rewrite IHp; route_eq_tac.
Qed.

Instance AbelianRoute : Abelian_EMonoid Route. 
  split;  apply app_comm.
Qed.


























 


  


