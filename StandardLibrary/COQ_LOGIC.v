Set Implicit Arguments.
Require Export Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Inductive True: Prop :=
I: True.

Inductive False : Prop := .

Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

Hint Unfold not: core.

Inductive and (A B:Prop) :Prop :=
  conj : A-> B -> A /\B

where "A /\ B" := (and A B) : type_scope.

Section Conjunction.
  Variables A B :Prop.
  Theorem proj1 : A/\B -> A.
  Proof.
  (*destruct 1.
  trivial.  
  *)  
  intro H1.
  destruct H1.
  exact H.
  Qed.
  Theorem proj2 : A /\ B -> B.
  Proof.
  intro H1.
  induction H1.
  exact H0.
Qed.
End Conjunction.

Inductive or (A B: Prop):Prop :=
|or_introl : A -> A \/ B
|or_intror : B -> A \/ B
where "A \/ B" := (or A B) : type_scope.

Definition iff (A B:Prop) := (A -> B) /\ (B->A).
Notation "A <-> B" := (iff A B) : type_scope.
Section Equivalence.
Variables A B C:Prop.
Theorem iff_refl : forall A, A <->A.
Proof.
intro H1.
split.
trivial.
trivial.
Qed.
Theorem iff_trans : forall A B C: Prop, (A <-> B) -> (B <-> C) -> (A <-> C).
Proof.
split.
induction H.
induction H0.
intros until 1.
apply H0; apply H; exact H3.
intro P2.
apply H; apply H0; exact P2.
Qed.
Theorem iff_sym: forall A B: Prop, (A<->B) -> (B <->A).
Proof.
split.
apply H.
apply H.
Qed.
End Equivalence.

Hint Unfold iff: extcore.

Theorem and_iff_compat_l : forall A B C : Prop, (B <-> C) -> (A /\ B <-> A /\ C).
Proof.
constructor.
exists.
apply H0.
apply H; apply H0.
exists.
apply H0.
apply H; apply H0.
Qed.

Theorem and_iff_compat_r : forall A B C : Prop, (B<->C) -> (B/\A <-> C/\A).
Proof.
split.
split.
apply H; apply H0.
apply H0.
split.
apply H; apply H0.
apply H0.
Qed.

Theorem or_iff_compat_l : forall A B C: Prop, (B <-> C) -> (A \/ B <-> A \/ C).
Proof.
split.
intro P.
destruct P.
left.
exact H0.
right.
apply H; exact H0.
intro P.
destruct P.
left.
exact H0.
right.
apply H.
exact H0.
Qed.

Theorem or_iff_compat_r : forall A B C :Prop, (B <-> C) -> (B \/ A <-> C \/ A).
Proof.
split.
intro Q.
destruct Q.
left; apply H; exact H0.
right; exact H0.
intro Q.
destruct Q.
left; apply H; exact H0.
right; exact H0.
Qed.

Theorem imp_iff_compat_l : forall A B C : Prop, (B <-> C) -> ((A -> B) <-> (A -> C)).
Proof.
split.
intro Q.
intro Q2.
apply H; apply Q; exact Q2.
intros P P2.
apply H.
apply P.
exact P2.
Qed.

Theorem imp_iff_compat_r : forall A B C : Prop, (B <-> C) -> ((B -> A) <-> (C -> A)).
Proof.
  split.
  intro P.
  intro Q.
  apply P.
  apply H; exact Q.
  intro P2.
  intro Q.
  apply P2.
  apply H; exact Q.
Qed.

Theorem not_iff_compat : forall A B : Prop, (A <-> B) -> (~ A <-> ~B).
Proof.
  split.
  intro P1.
  unfold not.
  intro Q1.
  elim P1.
  apply H.
  exact Q1.
  intro P2.
  unfold not.
  intro Q2.
  elim P2.
  apply H; exact Q2.
Qed.

Theorem neg_false : forall A : Prop, ~A <-> (A <-> False).
Proof.
  split.
  split.
  intro P2.
  
  contradict H.
  unfold not.
  intro Q2.
  elim Q2.
  exact P2.
  intro P3.
  elim P3.
  intro Q3.
  unfold not.
  destruct Q3.
  exact H.
Qed.

Theorem and_cancel_l : forall A B C : Prop, (B->A) -> (C -> A) -> ((A /\B <-> A /\ C) <-> (B <-> C)).
Proof.
  exists.
  constructor.
  intro P1.
  apply H1.
  split.
  apply H.
  exact P1.
  exact P1.
  intro P2.
  apply H1.
  split.
  apply H0.
  exact P2.
  exact P2.
  exists.
  constructor.
  destruct H2.
  exact H2.
  apply H1; apply H2.
  split.
  apply H2.
  apply H1; apply H2.
Qed.

Theorem and_cancel_r : forall A B C :Prop, (B->A) -> (C -> A) -> ((B /\ A <-> C /\ A) <-> (B <->C)).
Proof.
  split.
  split.
  intro P1.
  destruct H1.
  destruct H1.
  split.
  exact P1.
  apply H.
  exact P1.
  exact H1.
  destruct H1.
  intro P2.
  
  destruct H1.
  split.
  
  destruct H2.
  split.
  exact P2.
  apply H0.
  exact P2.
  exact H1.
  destruct H2.
  split.
  exact P2.
  apply H0.
  exact P2.
  exact H2.
  destruct H2.
  split.
  exact P2.
  exact H3.
  exact H2.
  split.
  split.
  destruct H2.
  apply H1.
  exact H2.
  destruct H2.
  exact H3.
  split.
  destruct H2.
  Focus 2.
  destruct H2.
  exact H3.
  apply H1.
  exact H2.
  Qed.

Theorem and_comm: forall A B : Prop, A /\ B <-> B /\ A.
Proof.
  split.
  split.
  destruct H.
  exact H0.
  destruct H.
  exact H.
  split.
  destruct H.
  exact H0.
  destruct H.
  exact H.
Qed.

Theorem and_assoc : forall A B : Prop, A /\ B <-> B /\ A.
Proof.
  split.
  split.
  destruct H.
  exact H0.
  destruct H.
  exact H.
  split.
  destruct H.
  exact H0.
  destruct H.
  exact H.
Qed.

Theorem or_cancel_l : forall A B C : Prop,
  (B -> ~ A) -> (C -> ~ A) -> ((A \/ B <-> A \/ C) <-> (B <-> C)).
Proof.
  intros ? ? ? Fl Fr; split; [ | apply or_iff_compat_l]; intros [Hl Hr]; split; intros.
  { destruct Hl; [ right | destruct Fl | ]; assumption. }
  
  { destruct Hr; [ right | destruct Fr | ]; assumption. }
Qed.
(* Goal forall A B: Prop, A/\B.
Proof.
  intro P0.
  intro P1.
  
  exists.
  intro H.
[H1 H2].
Check {.
   *)
  

  (*
http://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf
https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.Init.Logic.html
https://coq.inria.fr/distrib/current/stdlib/Coq.Init.Logic.html
https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html#simplegoals
*)

Theorem or_cancel_r : forall A B C: Prop, (B-> not A) -> (C -> not A) -> ((B \/ A <-> C \/ A) <-> (B <-> C)).
Proof.
  intros ? ? ? Fl Fr; split; [ | apply or_iff_compat_r]; intros [Hl Hr]; split; intros.
  { destruct Hl; [ left | | destruct Fl ]; assumption. }
  { destruct Hr; [ left | | destruct Fr ]; assumption. }
Qed.
Theorem or_cancel_r2 : forall A B C: Prop, (B-> not A) -> (C -> not A) -> ((B \/ A <-> C \/ A) <-> (B <-> C)).
Proof.
  intros *.
  intros Fl Fr.
  split.
  intro P1.
  Focus 2.
  apply or_iff_compat_r.
  split.
  intro Hl.
  Focus 2.
  intro Hr.
  Unfocus.
  intros.
  Admitted.
(*   Focus 2.
  (* exists. *)
  induction 1.
  induction H1.
  induction H2.
  split.
  intro P1.
  exact H1.
  intro P2.
  exact H2.
  split.
  intro P3.
  exact H1.
  intro P4.
  induction H.
  Focus 2.
  exact H2.
  Focus 2.
  left; exact H1.
  Focus 3.
  destruct H2.
  Unfocus.
  Focus 2.
  induction H2.
  split.
  intro P1.
  Focus 2.
  intro P2.
  exact H2.
  Focus 3.
  right; apply H1.
  Focus 2.
  split.
  intro P1.
  Focus 2.
  intro P1.
  Unfocus.
  Unfocus.
  induction H.
  Focus 2.
  exact H1.
  exact H2.
  destruct H.
  exact P1.
  exact H1.
  Unfocus.
  Focus 4.
  left; exact H1.
  Focus 5.
  destruct 1.

  split.
  induction 1.
  Focus 2.
  right; exact H3.
  Focus 2.
  induction 1.
  Unfocus.
  Focus 3.
  right; exact H3.
  Unfocus.
  Focus 4.
  right; exact H1.
  Focus 3.
  induction H.
  induction H0.
  Unfocus.
  induction H0.
  exact P4.
  exact H2.
  Focus 3.
  Unfocus.
  Focus 6.
  left; apply H2; exact H3.
  Focus 5.
  left; apply H1; exact H3.
  Focus 4.
  induction H0.
  Unfocus.
  auto.
  Admitted. *)


Theorem or_comm: forall A B : Prop, (A\/B) <-> (B\/A).
Proof.
  constructor.
  induction 1.
  right; exact H.
  left; exact H.
  induction 1.
  right; exact H.
  left; exact H.
Qed.

Theorem or_assoc : forall A B C :Prop, (A\/B) \/ C <-> A \/ B \/ C.
Proof.
  intros; split; [ intros [[?|?]|?] | intros [?|[?|?]]].
  + left; assumption.
  + right; left; assumption.
  + right; right; assumption.
  + left; left; assumption.
  + left; right; assumption.
  + right; assumption.
Qed.


(*   intros A B C.
  split.
  right.
  induction H.
  left.
  induction H.
  Focus 2.
  exact H.
  Focus 2.
  right; exact H.
  Focus 2.
  destruct 1.
  left; left; exact H.
  induction H.
  left; right; exact H.
  right; exact H.
  Admitted. *)

Theorem iff_and : forall A B: Prop, ( A <-> B) -> (A -> B) /\ (B -> A).
Proof.
  constructor.
  destruct H.
  exact H.
  destruct H.
  exact H0.
Qed.

Theorem iff_to_and : forall A B : Prop, (A<-> B) <-> (A -> B) /\ (B -> A).
Proof.
  constructor.
  induction 1.
  split.
  exact H.
  exact H0.
  split.
  destruct H.
  exact H.
  destruct H.
  exact H0.
Qed.

Definition IF_the_else ( P Q R: Prop) := P /\ Q \/ ~P/\R.

Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3) ( at level 200, right associativity): type_scope.

Inductive ex (A:Type) (P: A -> Prop) : Prop := ex_intro : forall x: A, P x -> ex (A:=A) P.

Section Projections.
Variables (A:Prop) (P:A-> Prop).
  Definition ex_proj1 (x:ex P) : A := match x with ex_intro _ a _ => a end.
  Definition ex_proj2 (x:ex P) : P (ex_proj1 x) := match x with ex_intro _ _ b => b end.
End Projections.

Inductive ex2 (A:Type) (P Q: A -> Prop) : Prop := ex_intro2 : forall x:A, P x -> Q x -> ex2 (A:=A) P Q.
Definition all (A:Type) (P:A -> Prop) := forall x:A, P x.
Notation "'exists' x .. y , p" := (ex (fun x => .. ( ex (fun y => p)) ..)) (at level 200, x binder, right associativity, format "'[' 'exists' '/' x .. y , '/ ' p ']'") : type_scope.
Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x ident, A at level 200, p at level 200, right associativity,
    format "'[' 'exists2' '/ ' x : A , '/ ' '[' p & '/' q ']' ']'")
  : type_scope.

Notation "'exists2' ' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x strict pattern, p at level 200, right associativity) : type_scope.
Notation "'exists2' ' x : A , p & q" := (ex2 (A:=A) (fun x => p) (fun x => q))
  (at level 200, x strict pattern, A at level 200, p at level 200, right associativity,
    format "'[' 'exists2' '/ ' ' x : A , '/ ' '[' p & '/' q ']' ']'")
  : type_scope.

Section universal_quantification.
Variable A:Type.
Variable P: A->Prop.

Theorem inst : forall x:A, all (fun x => P x) -> P x.
Proof.
  intros *.
  intro Q1.
  apply Q1.
Qed.

Theorem gen : forall (B:Prop) (f:forall y:A, B -> P y), B -> all P.
Proof.
  intros *.
  intro Q1.
  intro Q2.
  intro Q3.
  apply Q1.
  exact Q2.
Qed.

End universal_quantification.


Inductive eq (A:Type) (x:A) : A -> Prop := eq_refl : x = x :> A where "x = y :> A" := (@eq A x y): type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y :> T" := (~x = y :> T) :type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

Hint Resolve I conj or_introl or_intror : core.
Hint Resolve eq_refl: core.
Hint Resolve ex_intro ex_intro2: core.

Section Logic_lemmas.
  Theorem absurd: forall A C: Prop, A -> ~A -> C.
  Proof.
    intros *.
    intro P1.
    intro P2.
    contradict P2.
    unfold not.
    intro Q1.
    contradiction.
  Qed.

    Section equality.
      Variables A B : Type.
      Variables f : A->B.
      Variables x y z : A.
      Theorem eq_sym : x = y -> y = x.
      Proof.
        intro H0.
        replace x with y.
        reflexivity.
        destruct H0.
        reflexivity.
      Qed.
      
      Theorem eq_trans : x = y -> y = z -> x = z.
      Proof.
        induction 1.
        induction 1.
        reflexivity.
      Qed.
      
      Theorem eq_trans_r : x = y -> z = y -> x = z.
      Proof.
        induction 1.
        induction 1.
        reflexivity.
      Qed.
      
      Theorem f_equal : x = y -> f x = f y.
      Proof.
        induction 1.
        reflexivity.
      Qed.

      Theorem not_eq_sym : x <> y -> y <> x.
      Proof.
        intro P1.
        intro P2.
        induction P1.
        induction P2.
        reflexivity.
      Qed.

    End equality.

  Definition eq_sind_r : forall (A:Type) (x:A) (P:A -> SProp),  P x -> forall y : A, y = x -> P y.
  Proof.
    intros x y P.
    intro H0.
    intro M0.
    intro M1.
    induction M1.
    exact H0.
  Qed.

End Logic_lemmas.


Module EqNotations.
  Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew' H in '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew' [ P ] '/ ' H in '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew' <- H in '/' H' ']'").
  Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew' <- [ P ] '/ ' H in '/' H' ']'").
  Notation "'rew' -> H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' -> [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10, only parsing).

End EqNotations.

Import EqNotation
