Require Import Notations Logic Datatypes.
Require Decimal.
Local Open Scope nat_scope.

Definition t := nat.

Definition zero := 0.
Definition one := 1.
Definition two := 2.

Definition succ := S.
Definition pred n :=
  match n with
  | 0 => n
  | S u => u
  end.

Fixpoint add n m :=
match n with
| 0 => m
| S p => S (p+m)
end
where "n + m" := (add n m) : nat_scope.

Definition double n := n+n.

Fixpoint mul n m :=
  match n with
  | 0 => 0
  | S p => m + p * m
  end
where "n * m" := (mul n m) : nat_scope.

Fixpoint sub n m :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end
where "n - m" := (sub n m) : nat_scope.

Fixpoint eqb n m : bool :=
  match n, m with
    | 0, 0 => true
    | 0, S _ => false
    | S _, 0 => false
    | S n', S m' => eqb n' m'
  end.

Fixpoint leb n m : bool :=
  match n, m with
    | 0, _ => true
    | _, 0 => false
    | S n', S m' => leb n' m'
  end.

Definition ltb n m := leb (S n) m.

Infix "=?" := eqb (at level 70) : nat_scope.
Infix "<=?" := leb (at level 70) : nat_scope.
Infix "<?" := ltb (at level 70) : nat_scope.

Fixpoint compare n m : comparison :=
  match n, m with
    |0, 0 => Eq
    |0, S _ => Lt
    |S _, 0 => Gt
    |S n', S m' => compare n' m'
  end.

Infix "?=" := compare (at level 70) : nat_scope.

Fixpoint max n m :=
  match n, m with
    |0, _ => m
    | S n', 0 => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m :=
  match n, m with
    | 0, _ => 0
    | S n', 0 => 0
    | S n', S m' => S (min n' m')
  end.

Fixpoint even n : bool :=
  match n with
    |0 => true
    |1 => false
    |S (S n') => even n'
  end.

Definition odd n := negb (even n).

Fixpoint pow n m :=
  match m with
    |0 => 1
    |S m => n * (n^m)
  end
where "n ^ m" := (pow n m) : nat_scope.


(* It's nothing but definitions?
 *)
