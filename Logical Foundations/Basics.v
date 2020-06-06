Inductive bool : Type :=
  | true
  | false.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
 Notation "x && y" := (andb x y).
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition nandb (b1:bool) (b2:bool) : bool:= negb(b1 && b2).
(* 
Definition nandb (b1:bool) (b2:bool) : bool:=
match b2 with
  | false => true
  | true => b1
end.
 *)
Example test_nandb1: (nandb true false) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
simpl.
reflexivity.
Qed.
Example test_nandb3: (nandb false true) = true.
Proof.
reflexivity.
Qed.
Example test_nandb4: (nandb true true) = false.
Proof.
reflexivity.
Qed.

 Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := b1 && (b2 && b3).
 Example test_andb31: (andb3 true true true) = true.
Proof.
reflexivity.
Qed.

 Example test_andb32: (andb3 false true true) = false.
Proof.
reflexivity.
Qed.

 Example test_andb33: (andb3 true false true) = false.
Proof.
reflexivity.
Qed.

 Example test_andb34: (andb3 true true false) = false.
Proof.
reflexivity.

Qed.

Fixpoint factorial (n:nat) : nat := 
  match n with
  | 0 => S 0
  | S m => S m * factorial m
(*   | S m => m * factorial(minus m 1) *)
  end.

 Example test_factorial1: (factorial 3) = 6.
Proof.
simpl.
reflexivity.
Qed.

 Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
simpl.
reflexivity.
Qed.
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
 Definition ltb (n m : nat) : bool := andb (leb n m) (negb(eqb n m)) .
 Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
 Example test_ltb1: (ltb 2 2) = false.
Proof.
reflexivity.
Qed.
 Example test_ltb2: (ltb 2 4) = true.
Proof.
reflexivity.
Qed.

 Example test_ltb3: (ltb 4 2) = false.
Proof.
reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
intros *.
induction 1.
destruct 1.
reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
intros until 1.
simpl.
rewrite H.
reflexivity.
Qed.
Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros *.
intros P0.
destruct c.
* reflexivity.
* destruct b. simpl in P0. apply P0. simpl in P0. apply P0.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros *.
  destruct n.
  *   simpl. reflexivity.
  * simpl. reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  repeat intros *.
  intro P0.
  intros *.
  rewrite P0.
  rewrite P0.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall(x : bool), f x = negb x) ->
  forall(b : bool), f (f b) = b.
Proof.
  intros *.
  intro P0.
  intro P1.
  repeat rewrite P0.
  destruct P1.
  * simpl. reflexivity.
  * simpl. reflexivity.
Qed.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros *.
  intro P0.
  induction b.
  * induction c.
  - reflexivity.
  - simpl in P0. symmetry in P0. apply P0.
  * simpl in P0. apply P0.
Qed. 

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

(* 
No clue, come back later. Maybe.
Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | A _ => B _
  | B _ => A _
  end.
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => 0
  | B n => S 0 + bin_to_nat n
  | A n => S 0 + bin_to_nat (B n)
end.
Compute bin_to_nat(Z).
Compute bin_to_nat(B Z).
Compute bin_to_nat(A (B Z)).
Compute bin_to_nat(B (B Z)).
Compute bin_to_nat(  A (A (A (B Z)))).
Compute bin_to_nat ( B (A (B Z)) ).


 *)

