From HoTT Require Import Overture.
Lemma paths_rew A a y P (X : P a) (H : a = y :> A) : P y.
Proof.
rewrite <- H.
apply X.
Qed.

Lemma paths_rew_r A a y P (X : P y) (H: a = y :> A) : P a.
Proof.
rewrite -> H.
apply X.
Qed.


Definition paths__ind' {A: Type} (P : forall ( a b : A),
  (a=b) -> Type) : (forall ( a: A), P a a idpath)->
  forall (a b: A) (p : a = b), P a b p.
Proof.
intros.
rewrite <- p.

apply X.
Qed.

Definition paths_ind_r {A : Type} (a : A) (P: forall  b:A,
  b = a -> Type) ( u: P a idpath):
  forall ( y: A) (p: y = a), P y p.
Proof.
intro P0.
intro P1.
induction P1.
apply u.
Qed.


(* I don't understand how you can check a term's type?

a: A
P0 : A
P1 : P0 = a
P1 isn't inductive, it is P that is. 
  P1 is the second argument, in which a forall is being applied to
  Thus it is inductive within P.
    Why can't you do induction over P and it simply knows which argument?
 *)

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
  := match p with idpath => idpath end.
Global Arguments ap {A B}%type_scope f%function_scope {x y} p%path_scope.

Notation ap01 := ap (only parsing).
Definition pointwise_paths A (P : A -> Type) (f g : forall x, P x)
  := forall x, f x = g x.

(* I fucked up on this one. It seemed like everything wasn't
  an inductive type.
 *)
Definition pointwise_paths_concat {A} {P : A -> Type} {f g h : forall x, P x}
  : pointwise_paths A P f g -> pointwise_paths A P g h
    -> pointwise_paths A P f h := fun p q x => p x @ q x.

Global Instance reflexive_pointwise_paths A P
  : Reflexive (pointwise_paths A P).
Proof.
intros ?.
intros ?.
reflexivity.
Qed.
(* Question: Why does intros ? work but not intros?
?: behaves like a place holder(?)
  wildcard equivalent?

intros *: intro 0 or more times
  https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form
intros ?: Once or none.
  Source: https://www.rexegg.com/regex-quickstart.html

BNF specifies the '+' is like '?' right?

"* introduces one or more quantified variables from the result until there are no more quantified variables"
"? — let Coq choose a name"
https://coq.inria.fr/refman/proof-engine/tactics.html#intropatterns
Yikes, that was more simple than I was making it.

 *)

Global Instance transitive_pointwise_paths A P: Transitive ( pointwise_paths A P).
Proof.

intros f g h.
apply pointwise_paths_concat.
(* 
My solution:
intros ?.
intros ?.
intros ?.
intros ?.
intros ?.
intros ?.
rewrite X.
rewrite X0.
reflexivity. *)
Qed.

Global Instance symmetric_pointwise_paths A P: Symmetric (pointwise_paths A P).
Proof.
intros ? ? p ?.
symmetry.
apply p.

(* 
My solution:
intros f g.
intros ?.
intros ?.
rewrite X.
reflexivity. *)
Qed.

Definition apll {A B} {f g : A-> B} (h: f=g) {x y : A} (p:x=y) : f x = g y.
Proof.
case h, p.
reflexivity.
(* my solution:
rewrite p.
rewrite h.
reflexivity.
 *)Qed.

Definition issig_contr ( A : Type):{x : A & forall y, x =y} <~> Contr A.
Proof.
Print issig.
issig.
Qed.
(* Notes: No fucking clue how this one works.
 *)

Definition issig_equiv ( A B : Type) :{f : A -> B & IsEquiv f} <~> Equiv A B.
Proof.
issig.
Qed.
(* Once again, math magic
*)

Definition issig_isequiv {A B : Type} (f : A -> B) : {g: B -> A & 
  {r : Sect g f & { s : Sect f g & forall x : A, r ( f x) = ap f (s x)}}}
<~> IsEquiv f.
Proof.
issig.
Qed.
Definition inv_pV {A : Type} { x y z : A} (p : x = y) ( q : z = y) :
  (p @ q^)^ = q @ p^.
Proof.
destruct p. destruct q. reflexivity.

(* My solution:
induction p.
induction q.
simpl.
reflexivity. *)
Qed.

Definition inv_VV {A : Type} {x y z : A} (p : y = x) ( q : z = y) :
  (p^ @ q^)^ = q @p.
Proof.
induction p. induction q. reflexivity.
Qed.

From HoTT Require Import PathGroupoids.
Definition moveR_Mp {A : Type} {x y z : A} (p : x = z) (q: y =z) (r: y=x):
  p = r^ @ q -> r @ p =q.
Proof.
destruct r.
intro h.
exact (concat_1p _ @ h @ concat_1p _).

(* My solution:
intros ?.
destruct r.
destruct p.
simpl.
rewrite X.
rewrite <- q.
simpl.
reflexivity. *)
Qed.
(* Wow, made that more difficult than it should've
 *)

Definition moveR_pM {A : Type} {x y z : A} (p : x = z) (q: y = z)
  (r : y = x): r = q@p^ -> r @ p = q.
Proof.
destruct p.
intro h.
apply (concat_p1 _ @ h @ concat_p1 _).
(*
My solution:
intros ?.
destruct r. destruct p.
simpl.
rewrite X.
rewrite <- q.
simpl.
reflexivity.
 *)
Qed.
(* 
Notes: Treated it just like moveR_Mp
 *)

Definition moveR_Vp { A : Type} {x y z : A} ( p : x = z) ( q : y = z)
(r : x = y) : p = r @ q -> r^ @ p = q.
Proof.
destruct r.
intro h.
apply (concat_1p _ @ h @ concat_1p _).
(* 
My solution:
intros ?.
induction p. induction r.
simpl.
rewrite X.
rewrite <- q.
simpl.
reflexivity. *)
Qed.

Definition moveR_pV { A: Type} {x y z: A} (p : z = x) ( q: y = z)
(r : y = x) : r = q @ p -> r @ p^ = q.
Proof.
destruct p. destruct q.
simpl.
intro Q0.
rewrite Q0.
simpl; reflexivity.
Qed.

Definition moveL_Mp {A: Type} {x y z : A} (p : x = z) (q : y =z) (r : y = x):
r^ @ q = p -> q = r@p.
Proof.
destruct r.
intro h.
exact ((concat_1p _)^ @ h @ (concat_1p _)^).
(* My solution:
destruct r. destruct q.
simpl.
intro h.
rewrite <- h.
reflexivity. *)
Qed.

Definition moveL_pM {A : Type} {x y z : A} (p : x = z) ( q : y = z) (r : y = x):
  q @ p^ = r -> q = r @ p.
Proof.
destruct p.
intro h.
apply ((concat_p1 _)^ @ h @ (concat_p1 _)^ ).
(*my solution:
destruct p. destruct q.
simpl; intro h.
rewrite <- h; simpl; reflexivity.
 *)
Qed.

Definition moveL_Vp {A: Type} {x y z: A} (p : x = z) ( q : y = z)(r : x = y):
r @ q = p-> q = r^ @ p.
Proof.
destruct r.
intro h.
apply ((concat_1p _)^ @ h @ (concat_1p _)^).
Qed.
(* OHHHHHHH I see what I'm doing wrong here.
  1p != p1
*)
Definition moveL_pV {A : Type} {x y z : A} (p : z = x) ( q : y = z) (r : y = x):
  q @ p = r -> q = r @ p^.
Proof.
destruct p.
intro h.
apply ((concat_p1 _)^ @ h @ (concat_p1 _)^ ).
Qed.

Local Open Scope path_scope.


Definition moveL_1M {A : Type} {x y : A} (p q : x = y) :
  p @ q^ = 1-> p = q.
Proof.
destruct q.
intro h.
apply ((concat_p1 _)^ @ h).
Qed.

Definition moveL_M1 {A: Type} {x y : A} (p q : x = y) :
  q^ @ p = 1 -> p = q.
Proof.
destruct q.
intro h. apply ((concat_1p _)^ @ h).
Qed.

Definition moveL_1V {A : Type} {x y : A} (p : x = y) ( q: y = x):
  p@ q = 1 -> p = q^.
Proof.
destruct q.
intro h.
apply ((concat_p1 _)^ @ h).
Qed.

Definition moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  q @ p = 1 -> p = q^.
Proof.
destruct q.
intro h.
apply ((concat_1p _)^ @ h).
Qed.

Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
destruct p.
intro h.
apply (h @ (concat_1p _)).
Qed.

Definition moveR_1M {A : Type} {x y: A} (p q : x = y) : 
  1 = q @ p^ -> p = q.
Proof.
destruct p.
intro h.
apply (h @ (concat_p1 _)).
Qed.

Definition moveR_1V {A : Type} {x y : A} (p : x = y) ( q: y = x):
  1 = q @ p -> p^ = q.
Proof.
destruct p.
intro h.
simpl.
apply (h @ (concat_p1 _)).
Qed.

Definition moveR_V1 {A : Type} {x y : A} (p : x = y) (q:y = x):
  1 = p @ q -> p^ = q.
Proof.
destruct p.
intro h.
apply (h @ (concat_1p _)).
Qed.

(* Definition moveR_transport_p {A : Type} (P: A-> Type) {x y : A}
  (p : x = y) ( u : P x) (v : P y) : u = p^ # v -> p # u = v.
Proof.
destruct p.
simpl.
apply idmap.
Qed.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p # v -> p^ # u = v.
Proof.
destruct p.
simpl.
apply idmap.
Qed.


Definition moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : p # u = v -> u = p^ # v.
Proof.
destruct p.
simpl.
apply idmap.
Qed.

Definition moveL_transport_p {A:Type} (P : A -> Type) {x y : A} (p : y = x)
  (u : P x) ( v : P y):
  p^ # u = v -> u = p # v.
Proof.
induction p.
simpl.
apply idmap.
Qed. *)
Definition moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : u = p^ # v -> p # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p # v -> p^ # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : p # u = v -> u = p^ # v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : p^ # u = v -> u = p # v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveR_transport_p_V {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : u = p^ # v)
  : (moveR_transport_p P p u v q)^ = moveL_transport_p P p v u q^.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveR_transport_V_V {A:Type} (P : A -> Type) {x y:A}
  (p : y =x) (u : P x) (v : P y) (q : u = p#v)
  : (moveR_transport_V P p u v q)^ = moveL_transport_V P p v u q^.
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Definition moveL_transport_V_V {A: Type} (P : A -> Type) {x y:A}
  (p : x = y) ( u : P x) (v : P y) (q : p # u = v)
  : (moveL_transport_V P p u v q)^ = moveR_transport_V P p v u q^.
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Definition moveL_transport_p_V { A : Type} (P : A -> Type) {x y : A}
  (p : y = x) ( u : P x) ( v : P y) (q : p^ # u = v)
  : (moveL_transport_p P p u v q)^ = moveR_transport_p P p v u q^.
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Definition ap_p_pp {A B: Type} (f : A -> B) {w : B} {x y z:A}
  (r : w = f x) ( p : x = y) ( q: y = z):
  r @ (ap f ( p @ q)) = (r @ ap f p) @ ( ap f q).
Proof.
destruct p, q.
simpl.
apply ( concat_p_pp r 1 1).
(* My solution:
destruct p.
destruct q.
unfold ap.
simpl.
destruct r.
simpl.
reflexivity. *)
Qed.

Definition ap_pp_p {A B : Type} (f : A -> B) {x y z : A} {w : B}
  (p : x = y) (q : y = z) (r : f z = w) :
  (ap f ( p @ q)) @ r = (ap f p) @ (ap f q @ r).
Proof.
destruct p, q.
simpl.
apply (concat_pp_p 1 1 r).
Qed.

Definition ap_homotopic{A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  : (ap f q) = (p x) @ (ap g q) @ (p y)^.
Proof.
apply moveL_pV.
apply concat_Ap.
(* My solution:
destruct q.
simpl.
destruct p.
simpl.
reflexivity.
 *)
Qed.

Definition ap_homotopic_id {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y):
  (ap f q) = (p x) @ q @ (p y)^.
Proof.
apply moveL_pV.
apply concat_A1p.
(* My solution:
destruct q. destruct p.
simpl.
reflexivity.
 *)
Qed.

Definition concat_pA_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w z : B} (r : w = f x) (s : g y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (ap g q @ s).
Proof.
destruct q, s; simpl.
repeat rewrite concat_p1.
reflexivity.

(* destruct s, q.
simpl.
destruct p, r.
reflexivity.
 *)
Qed.
Definition concat_pA_p {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w : B} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ ap g q.
Proof.
destruct q; simpl.
repeat rewrite concat_p1.
reflexivity.
(* destruct q.
simpl.
destruct p, r.
reflexivity.
 *)
Qed.

Definition concat_A_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {z : B} (s : g y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (ap g q @ s).
Proof.
destruct q.
simpl.
destruct s.
simpl.
destruct p.
reflexivity.
Qed.

Definition concat_pA1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = f x) (s : y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (q @ s).
Proof.
destruct s; simpl.
destruct q; simpl.
destruct p; simpl.
reflexivity.
Qed.

 Definition concat_pp_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = x) (s : g y = z)
  :
  (r @ p x) @ (ap g q @ s) = (r @ q) @ (p y @ s).
Proof.
destruct s; simpl.
destruct q; simpl.
destruct p; simpl.
reflexivity.
Qed.

Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ q.
Proof.
(*  destruct s; simpl. *)
destruct q; simpl.
destruct p; simpl.
reflexivity.
Qed.
Definition concat_A1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {z : A} (s : y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (q @ s).
Proof.
destruct s; simpl.
destruct q; simpl.
destruct p; simpl.
reflexivity.
Qed.

Definition concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
  (r @ p x) @ ap g q = (r @ q) @ p y.
Proof.
destruct q; simpl.
destruct p; simpl.
reflexivity.
Qed.

Definition concat_p_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {z : A} (s : g y = z)
  :
  p x @ (ap g q @ s) = q @ (p y @ s).
Proof.
destruct s; simpl.
destruct q; simpl.
destruct p; simpl.
reflexivity.
Qed.

Lemma concat_1p_1 {A} {x : A} (p : x = x) (q : p =1)
  : concat_1p p @ q = ap (fun p' => 1 @ p')q.
Proof.
rewrite <- (inv_V q).
destruct q^.
reflexivity.
Qed.
(* 
1. clearbody
  Takes a definition to an assumption
So much for so little.
  Why?
 *)

Lemma concat_p1_1 {A} {x : A} (p : x = x) (q : p = 1)
  : concat_p1 p@q = ap ( fun p' => p' @ 1) q.
Proof.
rewrite <- (inv_V q).
destruct q^.
reflexivity.
Qed.
(* I must be missing why they are doing it a different way.
  Need to look at how 'automatic' tactics evaluate later
 *)

Definition apD10_pp {A} {B:A->Type} {f f' f'' : forall x, B x}
  (h:f=f') (h' : f' = f'') (x:A):
  apD10 (h @ h') x = apD10 h x @ apD10 h' x.
Proof.
destruct h.
destruct h'.
simpl.
reflexivity.
Qed.

Definition apD10_ap_precompose {A B C} (f : A -> B) 
  {g g' : forall x: B, C x} (p: g = g') a :
  apD10 (ap ( fun h : forall x: B, C x => h oD f) p) a=
  apD10 p (f a).
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Definition apD10_ap_postcompose {A B C} (f : forall x, B x -> C)
  {g g' : forall x: A, B x} (p : g = g') a:
  apD10 (ap (fun h : forall x: A, B x => fun x => f x (h x)) p)
  a = ap ( f a)( apD10 p a).
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Definition transport_p_pp {A : Type} (P : A -> Type)
  {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
  (u : P x)
  : ap (fun e => e # u) (concat_p_pp p q r)
    @ (transport_pp P (p@q) r u) @ ap (transport P r) (transport_pp P p q u)
  = (transport_pp P p (q@r) u) @ (transport_pp P q r (p#u))
  :> ((p @ (q @ r)) # u = r # q # p # u) .
Proof.
destruct r, q, p.
simpl.
reflexivity.
Qed.

Definition transport_pVp {A} (P : A -> Type) {x y:A} (p:x=y) (z:P x)
  : transport_pV P p (transport P p z)
  = ap (transport P p) (transport_Vp P p z).
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Definition transport_VpV {A} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : transport_Vp P p (transport P p^ z)
    = ap (transport P p^) (transport_pV P p z).
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Definition ap_transport_transport_pV {A} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (e : transport P p u = v)
  : ap (transport P p) (moveL_transport_V P p u v e)
       @ transport_pV P p v = e.
Proof.
destruct p.
simpl.
destruct e.
simpl.
reflexivity.
Qed.

Definition moveL_transport_V_1 {A} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x)
  : moveL_transport_V P p u (p # u) 1 = (transport_Vp P p u)^.
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Definition paths_ind_r_transport {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P y)
  : paths_ind_r y (fun b _ => P b) u x p = transport P p^ u.
Proof.

(* Their solution:
by destruct p.
Defined.
 *)
(* What the fuck?
    Their solution is a bit fucked.
    Yikes.
 *)
destruct p.
simpl.
Admitted.

Definition ap11_is_ap10_ap01 {A B} {f g:A ->B} (h:f=g) {x y:A} (p:x=y)
: ap11 h p = ap10 h x @ ap g p.
Proof.
destruct p, h.
(* simpl. *)
reflexivity.
Qed.

Definition ap011 {A B C} (f : A -> B -> C) {x x' y y'} (p : x = x') (q : y = y')
  : f x y = f x' y'.
Proof.
destruct p, q.
reflexivity.
Qed.

Definition ap01D1 {A B C} (f : forall (a:A), B a -> C a)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: transport C p (f x y) = f x' y'.
Proof.
destruct p, q.
simpl.
reflexivity.

Set Nested Proofs Allowed.
Definition transport2_p2p {A : Type} (P : A -> Type) {x y : A} {p1 p2 p3 : x = y}
  (r1 : p1 = p2) (r2 : p2 = p3) (z : P x)
  : transport2 P (r1 @ r2) z = transport2 P r1 z @ transport2 P r2 z.
Proof.
destruct r1, r2.
simpl.
reflexivity.
Qed.

(* Barring what they are talking about with naming
    The notation of how variable -> thing that uses
    variable is really nice
 *)

Lemma ap_transport {A} {P Q : A -> Type} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = (p # (f x z)).
Proof.
induction p.
simpl.
reflexivity.
Qed.

Lemma ap_transportD {A : Type}
      (B : A -> Type) (C1 C2 : forall a : A, B a -> Type)
      (f : forall a b, C1 a b -> C2 a b)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C1 x1 y)
: f x2 (p # y) (transportD B C1 p y z)
  = transportD B C2 p y (f x1 y z).
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Lemma ap_transportD2 {A : Type}
      (B C : A -> Type) (D1 D2 : forall a, B a -> C a -> Type)
      (f : forall a b c, D1 a b c -> D2 a b c)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D1 x1 y z)
: f x2 (p # y) (p # z) (transportD2 B C D1 p y z w)
  = transportD2 B C D2 p y z (f x1 y z w).
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Lemma ap_transport_pV {X} (Y : X -> Type) {x1 x2 : X} (p : x1 = x2)
      {y1 y2 : Y x2} (q : y1 = y2)
: ap (transport Y p) (ap (transport Y p^) q) =
  transport_pV Y p y1 @ q @ (transport_pV Y p y2)^.
Proof.
destruct q.
simpl.
destruct p.
simpl.
reflexivity.
Qed.
Definition transport_pV_ap {X} (P : X -> Type) (f : forall x, P x)
  {x1 x2 : X} (p : x1 = x2)
  : ap ( transport P p) ( apD f p^) @ apD f p = transport_pV P p ( f x2).
Proof.
destruct p.
simpl.
reflexivity.
Qed.




Definition apD_pp {A} {P : A -> Type} (f : forall x, P x)
  {x y z : A} (p : x=y) (q : y = z):
  apD f ( p @ q) = transport_pp P p q ( f x) @
  ap (transport P q) ( apD f p) @ apD f q.
Proof.
destruct q.
Info 1 case p.
(* simpl. *)
(* simple refine p. *)
(* Info 2 destruct p. *)
simple refine 1.
Qed.

Definition apD_V {A} {P : A -> Type} (f : forall x, P x)
           {x y : A} (p : x = y)
  : apD f p^ = moveR_transport_V _ _ _ _ (apD f p)^.
Proof.
Info 1 destruct p.
Info 1 simpl.
Info 1 reflexivity.
Qed.

Definition transport_const {A B: Type} {x1 x2 : A} (p : x1 = x2) ( y: B)
  :transport ( fun x => B) p y = y.
Proof.
  destruct p.
  simpl.
  reflexivity.
Qed.

Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A-> B)
  (p : x = y) ( z : P ( f x)):
  transport (fun x => P (f x)) p z = transport P ( ap f p) z.
Proof.
destruct p.
simpl.
reflexivity.
Qed.

Lemma transportD_compose {A A'} B {x x' : A} (C : forall x : A', B x-> Type)
  (f : A -> A') (p : x = x') y (z : C (f x) y):
  transportD ( B o f) (C oD f) p y z
  = transport (C (f x')) (transport_compose B f p y)^ (transportD B C (ap f p)
  y z).
Proof.
  destruct p.
  simpl.
  apply (transport_const z).



(* Neat:
  https://www.youtube.com/channel/UCx9SG4xrWGD21YH_NiEctWw/videos

 *)
(* Are all of these just destruct _ and reflexivity?

 *)
(* 
TODO:
  1. Why/How does (concat_p1 _ @ h @ concat_p1 _) work?
 *)



Structured cospans:
  L: A -> X
    functor
  A: has finite colimits
  X: has finite colimits
  L: left adjoint
  
Q0 := symmetric monoidal category
  is a hypergraph category
  is also a symmetric monoidal double category with structure.


