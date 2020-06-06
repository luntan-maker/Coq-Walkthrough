Import EqNotations.
Section equality_dep.
  Variable A : Type.
  Variable B : A -> Type.
  Variable f : forall x, B x.
  Variables x y : A.


   Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
    Proof.
      intro H0.
      intro H1.
      intro H2.
      intro H3.
      induction 1.
      exact H3.
    Qed.
  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
    Proof.
    intro P0.
    intro P1.
    intro P2.
    intro P3.
    intro P4.
    intro P5.
    induction P5.
    exact P3.
  Qed.
  Definition eq_rect_r : forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y=x -> P y.
    Proof.
    intros *.
    intro Q0.
    intro Q1.
    intro Q2.
    induction Q2.
    exact Q0.
    Qed.

Import EqNotations.

Section equality_dep.
  Theorem f_equal_dep : forall (H: x = y), rew H in f x = f y.
  Proof.
    intros *.
    destruct H.
    reflexivity.
  Qed.
End equality_dep.

Section equality_dep2.
  Variable A' : Type.
  Variable B' : A' -> Type.
  Variable g : A -> A'.
  Variable p : forall a:A, B a -> B' (g a).
  Lemma f_equal_dep2 : forall {A A' B B'} (f : A -> A') (g : forall a:A, B a -> B' (f a))
    {x1 x2 : A} {y1 : B x1} {y2 : B x2} (H : x1 = x2),
    rew H in y1 = y2 -> rew f_equal f H in g x1 y1 = g x2 y2.
    Proof.
    intros *.
    intro Q0.
    destruct Q0.
    destruct H.
    reflexivity.
    Qed.
End equality_dep2.

Lemma rew_opp_r : forall A (P:A ->Type) (x y:A) (H: x=y) (a:P y), rew H in rew <- H in a = a.
Proof.
  intros *.
  destruct H.
  reflexivity.
Qed.

Lemma rew_opp_l : forall A (P:A->Type) (x y : A) (H: x = y) (a:P x), rew <- H in rew H in a = a.
Proof.
  intros *.
  destruct H.
  reflexivity.
Qed.

Theorem f_equal2: forall (A1 A2 B:Type) (f: A1 -> A2 -> B) (x1 y1 : A1) (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  intros *.
  induction 1.
  induction 1.
  reflexivity.
Qed.

Theorem f_equal3 : forall ( A1 A2 A3 B: Type) (f: A1 -> A2 -> A3 -> B) (x1 y1: A1) (x2 y2:A2) (x3 y3:A3), x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof.
  intros *.
  induction 1.
  induction 1.
  induction 1.
  reflexivity.
Qed.

Theorem f_equal4: forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B) (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4), 
x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof.
  repeat induction 1.
  reflexivity.
Qed.

Theorem f_equal5 : forall (A1 A2 A3 A4 A5 B:Type) (f: A1 -> A2 -> A3 -> A4 -> A5 -> B) (x1 y1 : A1) (x2 y2: A2) (x3 y3:A3) (x4 y4: A4) (x5 y5:A5),
x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof.
  repeat induction 1.
  reflexivity.
Qed.

Theorem f_equal_compose : forall A B C (a b: A) (f:A->B) (g: B->C) (e: a=b),
f_equal g (f_equal f e) = f_equal (fun a => g(f a)) e.
Proof.
  intros *.
  destruct e.
  simpl.
  reflexivity.
Qed.

Theorem eq_trans_refl_l : forall A (x y:A) (e:x=y), eq_trans eq_refl e = e.
Proof.
  intros *.
  destruct e.
  simpl.
  reflexivity.
Qed.

Theorem eq_trans_refl_r : forall A (x y:A) (e:x =y), eq_trans e eq_refl = e.
Proof.
  intros *.
  reflexivity.
Qed.

Theorem eq_sym_involutive : forall A (x y:A) (e:x=y), eq_sym (eq_sym e) = e.
Proof.
  intros *.
  destruct e.
  simpl.
  reflexivity.
Qed.

Theorem eq_trans_sym_inv_l : forall A (x y:A) (e: x=y), eq_trans (eq_sym e) e = eq_refl.
Proof.
  intros *.
  destruct e.
  simpl.
  reflexivity.
Qed.

Theorem eq_trans_sym_inv_r : forall A (x y:A) (e:x=y), eq_trans e (eq_sym e) = eq_refl.
Proof.
  intros *.
  destruct e.
  simpl.
  reflexivity.
Qed.

Theorem eq_trans_assoc : forall A (x y z t: A) (e:x=y) (e': y=z) (e'':z=t),
eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
Proof.
  intros *.
  destruct e''.
  destruct e'.
  destruct e.
  simpl.
  reflexivity.
Qed.

Theorem rew_map : forall A B (P:B->Type) (f:A->B) x1 x2 (H:x1 = x2) (y:P (f x1)),
rew [fun x => P (f x)] H in y = rew f_equal f H in y.
Proof.
  intros *.
  destruct H.
  reflexivity.
Qed.

Theorem eq_trans_map : forall {A B} {x1 x2 x3:A} {y1:B x1} {y2: B x2} {y3:B x3},
forall (H1: x1=x2) (H2:x2=x3) (H1': rew H1 in y1 =y2) (H2' : rew H2 in y2 = y3), rew eq_trans H1 H2 in y1 =y3.
Proof.
  intros *.
  repeat destruct 1.
  destruct H1.
  destruct H2.
  reflexivity.
Qed.

Theorem map_subst : forall {A} {P Q:A->Type} (f : forall x, P x -> Q x) {x y} (H: x=y) (z: P x),
  rew H in f x z = f y (rew H in z).
Proof.
  intros *.
  destruct H.
  simpl.
  reflexivity.
Qed.

Theorem map_subst_map : forall {A B} {P:A->Type} {Q:B->Type} (f:A->B) (g : forall x, P x -> Q (f x)),
forall {x y} (H: x=y) (z:P x), rew f_equal f H in g x z = g y (rew H in z).
Proof.
  intros *.
  destruct H.
  reflexivity.
Qed.

Lemma rew_swap : forall A (P:A->Type) x1 x2 (H:x1=x2) (y1: P x1) (y2:P x2), rew H in y1 = y2 -> y1 = rew <- H in y2.
Proof.
  intros *.
  destruct H.
  repeat induction 1.
  split.
Qed.
(* what the fuck?*)

Lemma rew_compose : forall A (P:A ->Type) x1 x2 x3 (H1: x1=x2) (H2:x2=x3) (y: P x1),
rew H2 in rew H1 in y = rew (eq_trans H1 H2) in y.
Proof.
  intros *.
  destruct H1.
  destruct H2.
  simpl.
  reflexivity.
Qed.

Theorem eq_id_comm_l : forall A (f:A->A) (Hf:forall a, a = f a), forall a, f_equal f (Hf a) = Hf (f a).
Proof.
  Admitted.
Set Nested Proofs Allowed.
Theorem eq_id_comm_r : forall A (f:A->A) (Hf:forall a, f a = a), forall a, f_equal f (Hf a) = Hf (f a).
Proof.
  intros *.
  Admitted.

Lemma eq_refl_map_distr : forall A B x (f:A->B), f_equal f (eq_refl x) = eq_refl (f x).
Proof.
  intros *.
  simpl.
  reflexivity.
Qed.

Lemma eq_trans_map_distr : forall A B x y z (f:A->B) (e:x=y) (e':y=z), f_equal f (eq_trans e e') = eq_trans (f_equal f e) (f_equal f e').
Proof.
  intros *.
  destruct e'.
  destruct e.
  simpl.
  reflexivity.
Qed.

Lemma eq_sym_map_distr : forall A B (x y:A) (f:A->B) (e:x=y), eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
  intros *.
  destruct e; simpl; reflexivity.
Qed.

Lemma eq_trans_sym_distr : forall A (x y z:A) (e:x=y) (e':y=z), eq_sym (eq_trans e e') = eq_trans (eq_sym e') (eq_sym e).
Proof.
  intros *.
  destruct e'; destruct e; simpl; reflexivity.
Qed.

Lemma eq_trans_rew_distr : forall A (P: A-> Type) (x y z: A) (e:x=y) (e':y=z) (k: P x), rew (eq_trans e e') in k = rew e' in rew e in k.
Proof.
  intros *.
  destruct e'; destruct e; simpl; reflexivity.
Qed.

Lemma rew_const: forall A P (x y:A) (e:x=y) (k:P), rew [fun _=>P] e in k = k.
Proof.
  intros *.
  destruct e.
  reflexivity.
Qed.

Notation sym_eq := eq_sym (only parsing).
Notation trans_eq := eq_trans (only parsing).
Notation sym_not_eq := not_eq_sym (only parsing).

Notation refl_equal := eq_refl (only parsing).
Notation sym_equal := eq_sym (only parsing).
Notation trans_equal := eq_trans (only parsing).
Notation sym_not_equal := not_eq_sym (only parsing).

Hint Immediate eq_sym not_eq_sym: core.

 Definition subrelation (A B : Type) (R R' : A->B->Prop) :=
  forall x y, R x y -> R' x y.

Definition unique (A : Type) (P : A->Prop) (x:A) :=
  P x /\ forall (x':A), P x' -> x=x'.

Definition uniqueness (A:Type) (P:A->Prop) := forall x y, P x -> P y -> x = y.

Notation "'exists' ! x , P" := (ex (unique (fun x => P)))
  (at level 200, x ident, right associativity,
    format "'[' 'exists' ! '/ ' x , '/ ' P ']'") : type_scope.
Notation "'exists' ! x : A , P" :=
  (ex (unique (fun x:A => P)))
  (at level 200, x ident, right associativity,
    format "'[' 'exists' ! '/ ' x : A , '/ ' P ']'") : type_scope.

(* Uniqueness is kind of fucked?
Lemma forall_exists_unique_domain_coincide :
  forall A (P:A->Prop), (exists! x, P x) ->
  forall Q:A->Prop, (forall x, P x -> Q x) <-> (exists x, P x /\ Q x).

Lemma unique_existence : forall (A:Type) (P:A->Prop),
  ((exists x, P x) /\ uniqueness P) <-> (exists! x, P x).
*)

Inductive inhabited (A:Type) : Prop := inhabits : A -> inhabited A.
Hint Resolve inhabits: core.
Lemma exists_inhabited : forall (A:Type) (P: A->Prop), (exists x, P x) -> inhabited A.
Proof.
  destruct 1.
  Admitted.

Lemma inhabited_covariant (C D: Type) : (C -> D) -> inhabited C -> inhabited D.
Proof.
  intro P0.
  intro P1.
  induction P1.
  split.
  apply P0; exact X.
Qed.

Lemma eq_stepl : forall (A: Type) (x y z : A), x=y -> x =z -> z=y.
Proof.
  intros *.
  induction 1.
  induction 1.
  reflexivity.
Qed.

Declare Left Step eq_stepl.
Declare Right Step eq_trans.

Lemma iff_stepl : forall A B C : Prop, (A <-> B) -> (A <-> C) -> (C <-> B).
Proof.
  intros *.
  induction 1.
  induction 1.
  split.
  intro Q0.
  apply H; apply H2; exact Q0.
  intro Q1.
  apply H1; apply H0; exact Q1.
Qed.

Declare Left Step iff_stepl.
Declare Right Step iff_trans.

Section ex.
Local Unset Implicit Arguments.
Definition eq_ex_uncurried {M: Type} (P : M -> Prop) {u1 v1 : M} {u2 : P u1} {v2 : P v1} (pq : exists p : u1 = v1, rew p in u2 = v2): ex_intro P u1 u2 = ex_intro P v1 v2.
Proof.
  induction pq.
  induction H.
  destruct x0.
  simpl.
  reflexivity.
Qed.

Definition eq_ex {A :Type} {P : A ->Prop} (u1 v1 : A) ( u2: P u1) (v2 : P v1) (p : u1 = v1) (q : rew p in u2 = v2) 
: ex_intro P u1 u2 = ex_intro P v1 v2 := eq_ex_uncurried P (ex_intro _ p q).
Definition eq_ex_hprop {A} {P : A -> Prop} (P_hprop : forall ( x:A) (p q : P x), p = q) ( u1 v1 : A) (u2: P u1) (v2 : P v1) (p : u1 = v1)
: ex_intro P u1 u2 = ex_intro P v1 v2 := eq_ex u1 v1 u2 v2 p (P_hprop _ _ _).
Section ex2.
  Local Unset Implicit Arguments.

  Definition eq_ex2_uncurried {A : Type} (P Q : A -> Prop) {u1 v1 : A}
             {u2 : P u1} {v2 : P v1}
             {u3 : Q u1} {v3 : Q v1}
             (pq : exists2 p : u1 = v1, rew p in u2 = v2 & rew p in u3 = v3)
  : ex_intro2 P Q u1 u2 u3 = ex_intro2 P Q v1 v2 v3.































