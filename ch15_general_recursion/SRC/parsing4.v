Require Export Arith Omega List.
Require Export Wellfounded.
Require Export parsing.



(* we need to establish that parsing, as described by the parse_rel
   relation is deterministic.  In other words, the relation actually
   represents a partial function. *)

 

Theorem parse_rel_fun :
 forall l l1 t1,
   parse_rel l l1 t1 -> forall l2 t2, parse_rel l l2 t2 -> l1 = l2.
Proof.
 intros l l1 t1 Hp1; elim Hp1.
 - intros l2 l3 l4 t2 t3 Hp2 Hrec2 Hp3 Hrec3 l5 t4 H'.
   inversion H'.
   match goal with Hid : parse_rel l2 (close:: _) _ |- _ =>
                   generalize (Hrec2 _ _ Hid) end.
   intros heq1; injection heq1.
   intros heq2; subst l3.
   eapply Hrec3; eauto.

 -  intros l2 t2 Hp2; inversion Hp2; trivial.
 -  intros l0 l2 t2 Hp2; inversion Hp2; trivial.
Qed.


(* We actually develop a function that satisfies a stronger
   specification (see the type of parse_nest_aux2), using well-founded 
   induction.  The added information in the stronger type is that the
   string that remains to be parsed has a length that is less than or
   equal to the length of the input string.

   The first case concerns parsing an empty string, this is very
   simple. *)



Definition parse_nest_aux_nil :
  {l'': list par & {t:bin | parse_rel nil l'' t /\ length l'' <= length (A:=par) nil}}+
  {forall l'' t, ~parse_rel nil l'' t}.
Proof.
  left; exists (@nil par); exists L; split; auto.
  apply parse_leaf_nil.
Defined.

(* When parsing a string that starts with an open parenthesis, we need
   to perform two recursive calls, which may both fail.  Moreover, the 
   string that remains after the first recursive call needs to start
   with a closing parenthesis.  These constraints give three causes of 
   failures of the parser and we prove in each case that the string
   cannot be parsed if this happens.  This relies heavily on the fact
   that the parsing relation is deterministic. *)

Definition parse_nest_aux_open :
  forall l0 : list par,
  (forall l' : list par,
     length l' < S (length l0) ->
     {l'' : list par &
     {t : bin | parse_rel l' l'' t /\ length l'' <= length l'}}+
     {(forall (l'':list par)(t:bin), ~parse_rel l' l'' t)})->
  {l'' : list par &
  {t : bin |
  parse_rel (open::l0) l'' t /\ length l'' <= S (length l0)}}+
  {(forall (l'':list par)(t:bin), ~parse_rel (open :: l0) l'' t)}.

(* We use the refine tactic and we hope this makes the algorithm
   clear: parse the well-parenthesized expression after the opening
   parenthesis, check it is followed by a closing parenthesis, then
   parse an other well-parenthesized expression.  If all this succeeds
   return a result (inleft), if not, return a failure (inright) *)
 refine
   (fun l0 rec =>
      match rec l0 _ with
      | inleft (existT _ (close::l1) (exist _ t1 (conj Hp Hl))) =>
        match rec l1 _ with
        | inleft (existT _ l2 (exist _ t2 (conj Hp2 Hl2))) =>
          inleft _
              (existT  (fun l' => {t:bin | parse_rel (open::l0) l' t /\
                                          length l' <= S (length l0)})
                   l2 (exist _ (N t1 t2) _))
        | inright Hnp => inright _ (fun l'' t' Hp' => _)
        end
      | inleft (existT _ (open::l1) (exist _ t1 (conj Hp Hl))) => 
         inright _ (fun l'' t' Hp' => _)
      | inleft (existT _ nil (exist _ t1 (conj Hp Hl))) =>
         inright _ (fun l'' t' Hp' => _)
      | inright Hnp => inright _ (fun l'' t' Hp' => _)
      end);(auto ||
            (try (inversion Hp';
                  (try 
                    match goal with 
                    | id:parse_rel _ _ _ |- _ => 
                      generalize (parse_rel_fun _ _ _ Hp _ _ id);
                      discriminate
                    end)))).

 split;[eapply parse_node; eauto | auto].

 (* check that the second recursive call to the parser is done on a
    structurally smaller string. *)
 simpl in Hl; omega.

 match goal with
 | id:parse_rel _ (close::_) _ |- _ => 
   generalize (parse_rel_fun _ _ _ Hp _ _ id); intros Heq; 
   injection Heq; intros; subst; unfold not in Hnp; eapply Hnp; eauto
 end.

 unfold not in Hnp; eapply Hnp; eauto.
Defined.   
          
(* When a string starts with a close parenthesis, a new node in the
   "bin" data structure is cosntructed, but no character is removed to
   obtain the string that remains. *)

Definition parse_nest_aux_close :
  forall l0 : list par,
  (forall l' : list par,
     length l' < S (length l0) ->
     {l'' : list par &
     {t : bin | parse_rel l' l'' t /\ length l'' <= length l'}}+
     {(forall (l'':list par)(t:bin), ~parse_rel l' l'' t)})->
  {l'' : list par &
  {t : bin |
  parse_rel (close::l0) l'' t /\ length l'' <= S (length l0)}}+
  {(forall (l'':list par)(t:bin), ~parse_rel (close :: l0) l'' t)}.
Proof.
 intros l0 rec; left; exists (close::l0); exists L.
 split;[constructor | auto].
Defined.

(* This is the function that will be given as argument to
   the  well_founded_induction recursor.  *)

Definition parse_nest_aux :
 forall l: list par,
   (forall l':list par, length l' < length l ->
      {l'': list par & {t:bin | parse_rel l' l'' t /\
                 length l'' <= length l'}}+{forall l'' t, ~parse_rel l' l'' t}) ->
   {l'': list par & { t: bin | parse_rel l l'' t /\
       length l'' <= length l}}+{forall l'' t, ~parse_rel l l'' t}.
 refine
   (fun l => 
      match l return
        (forall l':list par, length l' < length l ->
         {l'': list par & {t:bin | parse_rel l' l'' t /\ length l'' <= length l'}}+
         {forall l'' t, ~parse_rel l' l'' t}) ->
          {l'': list par &
           {t: bin | parse_rel l l'' t /\ length l'' <= length l}}+
           {forall l'' t, ~parse_rel l l'' t}
      with
        nil => (fun rec => parse_nest_aux_nil)
      | cons open l0 => _
      | cons close l0 => _
      end); simpl.
 - apply parse_nest_aux_open.
 -  apply parse_nest_aux_close.
Defined.


Definition parse_nest_aux2 :
 forall l: list par,
  {l'':list par &
     {t:bin |
         parse_rel l l'' t /\ length l'' <= length l}}+
  {forall l'' t', ~parse_rel l l'' t'}.
exact 
 (well_founded_induction
    (wf_inverse_image (list par) nat lt (@length par) Wf_nat.lt_wf)
    (fun l =>
       {l'': list par &
         {t:bin | parse_rel l l'' t /\ length l'' <= length l}}+
       {forall l'' t', ~parse_rel l l'' t'})
    parse_nest_aux).
Defined.

Definition parse_nest :
 forall l: list par,
  {l'':list par &
   {t:bin | parse_rel l l'' t}}+{forall l'' t', ~parse_rel l l'' t'}.
Proof. 
intros l; elim (parse_nest_aux2 l).
- intros (l'', (t, (Hp, Hl))); left; exists l''; exists t; exact Hp.
- intros Hnp; right; exact Hnp.
Defined.

 