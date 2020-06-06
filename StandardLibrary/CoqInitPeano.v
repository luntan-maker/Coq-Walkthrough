Require Import Notations.
Require Import Datatypes.
Require Import Logic.
Require Coq.Init.Nat.

Open Scope nat_scope.

Definition eq_S := f_equal S.
Definition f_equal_nat := f_equal (A:=nat).

Hint Resolve f_equal_nat: core.

Notation pred := Nat.pred (only parsing).

Definition f_equal_pred := f_equal pred.

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  intros *.
  simpl.
  reflexivity.
Qed.

Definition eq_add_S n m (H: S n = S m) : n = m := f_equal pred H.
Hint Immediate eq_add_S: core.
Theorem not_eq_S : forall n m: nat, n<>m -> S n <> S m.
Proof.
  red.
  auto.
Qed.
Hint Resolve not_eq_S : core.

Definition IsSucc (n:nat) : Prop :=
  match n with
  | 0 => False
  | S p => True
  end.

Theorem O_S : forall n:nat, 0<> S n.
Proof.
  discriminate.
Qed.

Theorem n_Sn : forall n:nat, n<> S n.
Proof.
  auto.
Qed.

Notation plus := Nat.add (only parsing).
Infix "+" := Nat.add : nat_scope.

Definition f_equal2_plus := f_equal2 plus.
Definition f_equal2_nat := f_equal2 (A1:=nat) (A2:=nat) .
Hint Resolve f_equal2_nat: core.

Inductive bool: Set :=
  | true
  | false.

Lemma equality_of_functions_commutes:
  forall (f: bool->bool) x y,
    (f x) = (f y) -> (f y) = (f x).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma equality_of_functions_transits:
  forall (f: bool->bool) x y z,
    (f x) = (f y) ->
    (f y) = (f z) ->
    (f x) = (f z).
Proof.
  intros.
  rewrite H0 in H. (* or rewrite <- H0 *)
  assumption.
Qed.


Lemma xyz:
  forall (f: bool->bool) x y z,
    x  = y -> y = z -> f x = f z.
Proof.
  intros.
  cut (x = z).
  - intro. subst. reflexivity.
  - subst. reflexivity.
Qed.


Lemma plus_n_O : forall n:nat, n = n+0.
Proof.
  induction n.
  simpl.
  reflexivity.
  rewrite IHn.
  cut (n+0 = n).
  intro P1.
  rewrite P1.
  simpl.
  rewrite P1.
  reflexivity.
  symmetry.
  exact IHn.
Qed.
Hint Resolve plus_n_O eq_refl: core.
Lemma plus_O_n : forall n:nat, 0+n = n.
Proof.
  intro P0.
  simpl.
  reflexivity.
Qed.

Lemma plus_n_Sm : forall n m: nat, S (n+m) = n + S m.
Proof.
  induction n.
  simpl.
  reflexivity.
  intro P0.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
Hint Resolve plus_n_Sm: core.

Lemma plus_Sn_m : forall n m: nat, S n + m = S (n + m).
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Notation plus_0_r_reverse := plus_n_O (only parsing).
Notation plus_succ_r_reverse := plus_n_Sm (only parsing).

Notation mult := Nat.mul (only parsing).
Infix "*" := Nat.mul : nat_scope.

Definition f_equal2_mult := f_equal2 mult.
Hint Resolve f_equal2_mult: core.

Lemma mult_n_O : forall n: nat, 0 = n* 0.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  exact IHn.
Qed.
Hint Resolve mult_n_O : core.

Lemma mult_n_Sm : forall n m:nat, n*m + n = n * S m.
Proof.
  auto.
Qed.



