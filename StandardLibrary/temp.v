Theorem contradiction_implies_anything: forall P Q :Prop,
(P /\ ~P) -> Q.
Proof.
intros.
inversion H.
contradiction.
Qed.

Theorem double_neg: forall P : Prop,
P->~~P.
Proof.
intros.
intro P0.
contradiction.
Qed.

Theorem not_False : ~False.
Proof.
unfold not.
intros.
apply H.
Qed.


Theorem contrapositive: forall P Q: Prop,
(P->Q) -> ( ~Q -> ~P).
Proof.
intros P Q.
intro Imp.
unfold not.
intros.
apply H.
apply Imp.
apply H0.
Qed.

Theorem not_both_true_and_false: forall P : Prop, ~(P /\~P).
Proof.
intros.
unfold not.
intro P0.
apply P0.
induction P0.
exact H.
Qed.

Theorem excluded_middle_irrefutable: forall(P:Prop),
~~(P \/ ~ P).
Proof.
unfold not.
intros.
apply H.
right.
intro P0.
contradict H.
left; apply P0.
Qed.

Theorem not_false_then_true : forall b: bool,
 b <> false -> b = true.
Proof.
intro P0.
intro P1.
induction P0.
trivial.
contradiction.
Qed.

Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Import Coq.Init.Nat.
Require Import NAxioms NProperties OrdersFacts.
Theorem bi_induction:
forall A : nat -> Prop, Proper (eq ==> iff) A ->
A 0 -> (forall n : nat, A n <-> A (S n)) -> forall n : nat, A n.
Proof.
intros.
induction n.
apply H0.
symmetry in H1.
rewrite H1.
apply IHn.
Qed.


(* Q: What does bi_induction do?
      1. apply term.
          Category: tacn
          What: "applies to any goal"
          How: "tries to match the current goal against the conclusion of the type of term"
          Notes: If success, then make many subgoals. If fails, then each component of term matched to goal.
          Sources:https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.apply
      2. rewrite term.
          Category: tacn
          What: rewrites a goal(or hypo?) with the term given 
          How: "finds first subterm... in the goal"-replaces the resulting instances in the goal(?).
          Notes: Paraphrase- some varaibles are solved and some types become new subgoals.
          Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.rewrite
      3. symmetry in _.
          Category: tacn
          What: variant of symmetry. Applies symmetry to a hypothesis ident.
          How: Likely the same as symmetry.
          Notes: None
          Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.symmetry
    Summary:
      First we apply repeat intro until there is nothing left to intro in the goal.
      By applying induction n we create two new subgoals since n is a natural number
      We then apply a previously intro'ed term to the base case causing resolution.
      By using symmetry in the hypothesis we are able to utilize the bijection between A ( S n) and A n.
      Since there is a bijection between the two previously mentioned terms, and one of which is in the subgoal (alone)
        we can rewrite the subgoal as A n.
    This changes our subgoal to A n, which we apply IHn that was created from our 3rd step, this resolves the last subgoal.

Question: Why the fuck did the third step introduce the assumption from induction as well as the ident we were
          inducting over?

 *)

Definition recursion {A} : A -> (nat -> A -> A) -> nat -> A :=
  nat_rect (fun _ => A).
Theorem recursion_0:
forall {A} (a :A) (f : nat -> A -> A), recursion a f 0 = a.
Proof.
(* repeat intro. *)
intros.
simpl.
reflexivity.
Qed.

(* Q What does recursion_0 do?
      1. intros.
          Category: tacnv
          What: "repeats intro until it meets the head-constant"
          How: repeat intro
          Notes: Equivalent to repeat intro? Yes-based off of outcome.
                  Never reduces head-constants
                  Never fails
          Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.intros
  Q What is a head-constant?
    R: Term? "First element with default."       https://coq.inria.fr/refman/language/coq-library.html#index-25
    R: SearchHead term-no clue how it works. Treats the conclusion as a list of terms though.
    R: Winner winner: https://coq.github.io/doc/master/api/coq/Heads/index.html
        Allows for reformulation of what I am looking for.
    R: "The head-symbol of an applicative term is the symbol that occurs 
        at the leftmost-innermost position. This symbol is either a constant or a variable."
          Source: Functional And Logic Programming - Proceedings Of The Fuji International ...
                  Page: 317
    Notes: SearchHead will be useful!
            Somewhat more defined, good enough for now.
  Summary:
    *Pardon the 'we', old habits.*
    We constantly introduce variables to define things that are definable within the goal.
    we then simplify so we can read it better.
    Reflexivity finds an equivalence between the two terms in the equality. Then it removes the goal.
 *)
Theorem recursion_succ : 
forall {A} (Aeq : relation A) (a : A) (f : nat -> A -> A),
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n : nat, Aeq (recursion a f (S n)) (f n (recursion a f n)).
Proof.
Admitted.

Lemma pred_succ n : pred (S n) = n.
Proof.
simpl.
reflexivity.
Qed.

Lemma pred_0 : pred 0 = 0.
Proof.
simpl.
reflexivity.
Qed.

Lemma one_succ : 1 = S 0.
Proof.
reflexivity.
Qed.

Lemma two_succ : 2 = S 1.
reflexivity.
Qed.

Lemma add_0_l n : 0 + n = n.
Proof.
simpl.
reflexivity.
Qed.

Lemma add_succ_l n m : (S n) + m = S ( n + m).
Proof.
simpl.
reflexivity.
Qed.

Lemma sub_0_r n : n - 0 = n.
(* symmetry. *)
induction n.
simpl; reflexivity.
reflexivity.
Qed.



(* Q: What does the proof of sub_0_r explain? 
      1. symmetry
          Category: tacn
          What: changes the goal, dependent on equality.
          How: simply rewrites t=u as u=t
          Notes: A form of equality. Transitivity might be useful.
          Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.symmetry
      2. induction _
          Category: tacn
          What: Generates subgoal for each possible form of _(term)
            Requirement: Must be a term of inductive type
          How: See notes. Varied implementation depending on context and pattern used.
          Notes: Can use patters like "_" where the tactic looks for suitable subterms.
                  There are many variations. Should look over them whenever the need for induction arises.
          Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.induction
    Summary:
      By performing symmetry we make the equality as t = u as u = t.    Does nothing of value.
      This is followed by performing induction on n. In this case it is basic mathematical induction. 
        Base case := 0, inductive step := S n = n+1
      We recursively apply simplification (finding another readable form), 
        and reflexivity(similar to simplification with goal removal) to the base case.
      This process is then repeated in the inductive step.
*)



Lemma sub_succ_r n m : n - (S m) = pred ( n - m).
Proof.
destruct n.
destruct m.
simpl; reflexivity.
simpl; reflexivity.
Admitted.


Lemma mul_0_l n : 0 * n = 0.
Proof.
simpl; reflexivity.
Qed.

(* 
To make this easier in the future, try and use coq-dpdgraph
  Even if nothing comes from it, familiarization might be useful.

*)
(* 
  Q: What does the proof of mul_0_l explain?
    1. overarching structure _;_.
      Maybe a Notations with recursive patterns?
        Potential source: https://coq.inria.fr/refman/user-extensions/syntax-extensions.html
      Shot in the dark: Apply _ and _ recursively until there is no progress to be made on each goal.
      Found Print Grammar constr. andPrint Grammar pattern.
        To be used within a proof, each shows current stat of coq term parser and state of subparser of patterns.
        No clue what to do with it, but it's neat though.
      Fuck me, it's composition. Jesus.
        See: Strategies for rewriting - https://coq.inria.fr/refman/addendum/generalized-rewriting.html
    2. simpl
      Category: tacn
      What: "reduce a term to something still readable"
      How: "They perform a sort of strong normalization with two key differences"
      Notes: N/A
      Source:https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#coq:tacn.simpl

      
    3. reflexivity
      Category: tacn
      What: Checks if two things are equal.
      How: ?
      Notes:
        Equivalent to  'apply refl_equal'
      Source: https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#coq:tacn.reflexivity

  Q: What is strong normalization?
      Fuck. 
      Hail the almighty.
    Gist: 
      It is a property of a rewrite system.
      "If every sequence of rewrites eventually terminates with an irreducible term"
      normal form <-> an irreducible term
      untyped lambda calculus doesn't have the(any?) strong normalization property.
      lambda calc w/ normalization -> progr. language -> every programs terminates
      Source: https://en.wikipedia.org/wiki/Normalization_property_(abstract_rewriting)
      Neat stuff to look at: https://www.semanticscholar.org/search?q=type%20theory&sort=relevance
  Q: What does strong normalization mean in the context of reflexivity?
      It means that the process is finite and will terminate eventually.

  Q: What is refl_equal?
      refl_equal := eq_refl     https://coq.inria.fr/library/Coq.Init.Logic.html
      eq_refl index on coq gives the same entry as eq?
        Really not sure why though.
  Q: What can be gained from current understanding of refl_equal regarding reflexivity?
      It is a form of equality.

 *)

(* So how would I go about trying to understand what/how Coq is doing what it does?
    Try: Explain in common english what Coq is doing from a mathematical perspective.
      R: Simplify is reducing the goal to something that is readable, and still equivalent.
         Reflexivity is a form of equivalence, in which if the two objects are found to be equivalent the goal is removed.

 *)

(* Let's now work though some theorems proven in the github repo.
 *)

Theorem proj1 (A B : Prop) : A /\B -> A.
Proof.
  destruct 1; trivial.
Qed.

(* Q How was proj1 solved?
      1. destruct num
          Category: tacn
          What: "behaves as intros until num followed by destruct applied to the last introduced hypothesis."
          How: See ^
          Notes: Applies to any goal. destruction of a given numeral use destruct (num)
          Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.destruct
      2. trivial
          Category: tacn
          What: "A restricted form of auto that is not recursive and tries only hints that cost 0."
          How: ^
          Notes: See first question below. Cost is 0.
          Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.trivial
    1-1. destruct
          Category: tacn
          What: Behaves like induction, but inductive hypothesis is not generated.
          How: Really depends. Shot in the dark, destruct num -> [destruct term | destruct ident]
               The how isn't gone into much with documentation? Find other routes to get information other than coq
                references.
          Notes: "applies to any goal." "term must be inductive or co-inductive type" "tactic generates subgoals"
          Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.destruct
  Q: What is a cost in the context of a tactic using a hint?
      Hints more or less act like a path in ubuntu. In which when something is called it just iteratively goes through
      and find the file in each directory given.
  Q: The fuck is cost then?
      Context: Hints databases for auto/eauto
      Quote: "The cost of that hint is the number of subgoals generated by Apply term" 
      Source: https://www.fing.edu.uy/inco/grupos/mf/man/Coq/node.1.2.12.html
      Note: 'Print Hint *' displays all declared hints 
  Q: Alternative nity-grity documentation for coq tactics?
      Not nity-grity, but gives a different perspective: https://www.fing.edu.uy/inco/grupos/mf/man/Coq/toc.html
      Example: Destruct ident/num: https://www.fing.edu.uy/inco/grupos/mf/man/Coq/node.1.2.6.html
      Note: Actually a really **** nice resource!

  Summary:
    The ; allows for composition between the two tactics.
    destruct 1 applies destruct num. This is equivalent to destruct ident for the num-th dependent premises of the goal.
    trivial then iterates/applies through 0 cost hints in the auto hints library, this then resolves the subgoals.
 *)

Theorem iff_refl : forall A : Prop, A <-> A.
Proof.
  split; auto.
Qed.

(* Q: How does iff_refl work?
      1. split
          Category: tacn
          What: More or less
          How: Is a restricted form of constructor. Just use constructor 1.
          Notes: None. 
          Sources:https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.split
  Q What is a bindings list?
    It is a collection of references and terms. References can be either an ident or num. Ident is bound by term
  Q What is constructor 1?
    Deal with it later.
  Summary: split in this context allows for you to handle the bijection as two different parts. Auto iterates through
          a list of hints.
 *)

Theorem iff_trans : forall A B C: Prop, (A<->B) -> (B <->C) -> (A <->C).
Proof.
intros A B C [H1 H2] [H3 H4]; split; auto.
Qed.

(* Q: How does iff_trans work?
      1. intros _ _ _ [_ _] [_ _]
        Category: tacn
        What: "Matches one or more variables or hypotheses from the goal by matching the intro patterns."
        How: applies intro with some extra magic.
        Notes: Should look at intro patterns more.
        Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.intros
  Q: What patterns are there?
    Quite a few.

 *)

Require Import Coq.Init.Peano.
Theorem not_eq_S : forall n m : nat, n <> m -> S n <> S m.
Proof.
(* red. *)
red in |- *.
auto.
Qed.


(* 
Comments:
'red.' <-> 'red in |- *.' in this context.

Q: What does 'red' do?
    What: Replaces and then reduces some goals of a specific form.
    How: Reduction is done by bi-reduction rules(?)
    Source: https://www.fing.edu.uy/inco/grupos/mf/man/Coq/node.1.2.4.html#@default414
    Notes: None
Q: wtf is a bi-reduction rule?
    Context: Decision problems?
    Further: https://en.wikipedia.org/wiki/Decision_problem: https://en.wikipedia.org/wiki/Reduction_(complexity)
    Notes: Requires further investigation, not straight forward(?)
Q: What does 'in' mean?
    Category:tacn
    What: Generalizes hypothesis, performs tactic on goal, reintroduces generalized facts.
    How: given a pattern of 'tactic in ident' it applies generalizes the ident and performs 
          the given tactic on the goal.
    Source:https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#coq:tacn.in
    Notes:Shitty explanation of how, composition of smaller things that is semantically somewhat distinct.
            Tactics formed with 'do' can be used with in.
Q: In coq documentation what does notation like ^+, ^? mean?
    Fuck me, is this product/sum types?
      Shot in the dark: item^+ means item is cast in +?
    Church notation: with the types indicated by their subscripts
      Source: https://plato.stanford.edu/entries/type-theory-church/
    "A typed symbol is a symbol with a subscript from T"
      Source: https://arxiv.org/pdf/1703.02117.pdf
    "F^A type constructor F with type argument A."
    Subscript is referring to a structure. So a morphism_structure. 
      This seems different to how wikipedia was showing it, where you had item^model?
      Source: page 546, file:///home/a/Downloads/sofp%20(1).pdf
    Aren't the latter two contradicting each other over the same thing?
  Maybe just datatypes?
    thing(^type)(_signature)
    Source:https://coq.inria.fr/refman/language/coq-library.html#index-6

Why is this so hard to find?
  Is it assumed?

Q: What does '|-' mean in this context?
    Category:tacn
    What: A notation(?), means is provable from _
    How:  No clue, not even sure if this is right.
    Source:https://en.wikipedia.org/wiki/List_of_logic_symbols
    Notes: Not sure if taking what is in logic and shoving it into a proof assistant is valid.
Q: What does '*' mean after '|-'?
    Category:tacn
    What: allows for the tactic to be applied to the hypothesis as well as the list of names
    How: Does * refer to the hypothesis always?
    Source:https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#coq:tacn.in
    Notes: Kind of confused on this one.
Q: Does ^? mean optional in the 
    Let's not touch this for now.
Notes:
  +: sum type, corresponds to disjunction(or)
  *: product type, corresponds to conjucntion(and).
 *)

Theorem O_S : forall n : nat, 0<> S n.
Proof.
  discriminate.
Qed.


(* 
  Q: What does discriminate do?
    Comment: Is it seriously self referencing?
      Source: https://www.fing.edu.uy/inco/grupos/mf/man/Coq/node.1.2.8.html#@tactic68
    Category: tacn
    What: Depends. 
          If there is something in the hypothesis that discriminate is applicable to
            It behaves like discriminate ident.
          If the goal is of the form term <> term
            It behaves as 'intro ident; discriminate ident.'
    How:  See ^
    Notes:  None
    Sources: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.discriminate

 *)

Lemma mult_n_Sm : forall n m : nat, n * m + n = n * S m.
Proof.
intros; induction n as [ | p H]; simpl in |- *; auto.
destruct H.
rewrite <- plus_n_Sm.
apply (f_equal S).
pattern m at 1 3 in |- *.
Admitted.
(* 
generalize m:
1 subgoal
p, m : nat
______________________________________(1/1)
nat -> m + p * m + p = m + (p * m + p)
 *)

(* pattern m at 1 3 in |- *.
1 subgoal
p, m : nat
______________________________________(1/1)
(fun n : nat => n + p * m + p = n + (p * m + p)) m

Question:
  Anonymous lambda fn?

 *)
(* induction n as [ | p H].
  intros; induction n as [ | p H]; simpl in |- *; auto.
  destruct H; rewrite <- plus_n_Sm; apply (f_equal S).
  pattern m at 1 3 in |- *; elim m; simpl in |- *; auto.
Qed. *)
(* Summary:
intros introduces all the variables from the goal to the hypothesis
One of which is n, that we apply induction to. 
  The pattern is useless, and can be acheived with regular induction n.
  Scratch that, it names the hypothesis H, instead of  IHn.
  Also, it changes n -> p.
Likewise the 'simpl in |- *.' could just be simpl.
  This just makes it easier for us to read, largely.
destruct behaves like case ident; clear ident.
  Which just performs case analysis and clear removes the hypothesis ident.
rewrite <- allows you to specify which direction to substitute from.
  This is better than 
  'pose proof plus_n_Sm as H0. 
   pose proof (H0 n m) as H1; clear H0. 
   symmetry in H1; apply H1.'
apply (f_equal S) allows for a substitution to be done for S.
  It seems like the idea is to unfurl the function S.
    Why not unfold?

 *)
(* Goal: explain some of the patterns and terms
         then walk through what the proof is doing.
1. as
  What: Seems to be a way of describing a pattern
  How: Literally can be explained via regex.
  Note: None
  Source: https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.induction
2. [| p H]
  What: In the context it is a or_and_intropattern_loc.
  How:  Definition, either nothing will be done(?, from blank=nothing)
         or p H will be selected.
  Note:None.
  Source: https://coq.inria.fr/refman/proof-engine/tactics.html#grammar-token-or_and_intropattern_loc
3. rewrite
  What: Depends. Tactic.
  How:
  Note:
  Source:https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#coq:tacn.rewrite-ssreflect
https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.rewrite
4. <-
  What:Similar to dependent rewrite ->. In ocaml it is variable assignment/declaration
  How: Magic.
  Note: None really, it is defined more by the context than the symbol itself.
  Source:https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.dependent-rewrite
5. pattern
  What: No clue.
        Context of the code: Only the occurences of the num's are considered for
                             beta expansion.
  How: Applies a Beta expansion of the current goal.
  Note:None
  Source:https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.pattern
6. at
  What: Part of the pattern to match in
  How: Regex
  Note: Can't find it in ocaml reference or coq.
  Source: None

7. or_and_intropattern_loc
  What: a list containing or_and_intropattern and ident
  How: Definition
  Note: None
  Source: https://coq.inria.fr/refman/proof-engine/tactics.html#grammar-token-or_and_intropattern_loc
8. or_and_intropattern
  What:A list of conjunctive simple_intropatterns or a disjunctive list of 
        intropattern_list.
  How: Definition.
  Note:None
  Source: https://coq.inria.fr/refman/proof-engine/tactics.html#grammar-token-or_and_intropattern
9. simple_intropattern
    What: A list of a simple_intropattern_closed along with a single term.
    How:Definition
    Note:No clue wtf % term means in the brakets
    Source:https://coq.inria.fr/refman/proof-engine/tactics.html?highlight=#coq:tacv.apply-in-as
10. simple_intropattern_closed
    What: A list consisting of a naming_intropattern, wildcard, 
          or_and_intropattern, rewriting_intropatter, 
          and/or an injection_intropattern
    How: Definition magic
    Note: None
    Source: https://coq.inria.fr/refman/proof-engine/tactics.html#grammar-token-intropattern_list

n+1. dependent rewrite
    What:Tactic, applies to any goal. Exactly what depends on hypothesis.
    How: Rewrites, each term from an equality that is a sigma type is rewritten
    Note: Need to look at existT in more depth.
    Source:https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.dependent-rewrite

n+2. existT
    What:Term, can denote type? "existT is template universe polymorphic 
        on sigT.u0 sigT.u1"
    How: 
    Note: Why is it so difficult to find? wtf?
    Source:https://github.com/coq/coq/blob/3ae4231d30edfa928595b6fa886ce6df1a495089/test-suite/output/PrintInfos.out

n+3. Polymorphic Universe
    What: Paraphrasing - "Allows for definitions to be implicitly duplicated at different universe levels
          with the types they contain"
    How: An extension of 'this' leads ot said notion.
    Note: The paper is pretty decent.
    Source:https://ncatlab.org/nlab/show/universe+polymorphism
          http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=25E6B35E81C1D36D985AE394FA88536B?doi=10.1.1.38.8166&rep=rep1&type=pdf


Q: What does '::=' mean?
    What: Specifies what the term on the left is equivalent to, on the right.
    "The metasymbols ::= is to be interpreted as 'is defined as'"
    How: Magic.
    Notes:  None
    Source: https://www.cs.cornell.edu/courses/cs3110/2020sp/textbook/interp/bnf.html
            https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form
    This is in contrast to ':=' which is a means of defining something(?)
      Note: symbol derivation rule

Q: Wtf is a metalinguistic connector?
    Metalinguistic: Study of dialogue relationships between units of speech communication 
                    as manifestations and enactments of co-existence.
    Source:https://en.wikipedia.org/wiki/Metalinguistics
    Connector: Denotes a relation between two things.
    Source: http://www.helsinki.fi/varieng/series/volumes/08/lenker/

Q: Wtf is a symbol deriviation rule

Q: Since ::= doesn't mean 'list of ....' wtf are 
    the 'thing_of::= thing1\n thing2'?
    if all whitespace is the same then it means conjunction from BNF.
    
Q: 

Comments:
  Holy shit is + being expressed as ,?
  So it is saying ,"Hey the terms here are going to be conjunctive. Express
  it as thing1, thing2 for it to be taken as thing1 and thing2."
  Geniunely mentally deficient.

  In the future take the entire expression first, 
  and then break down what the smaller bits do.

  "Grammars are presented in Backus-Naur form (BNF)."
  Source: https://coq.inria.fr/distrib/current/refman/language/gallina-specification-language.html
          https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form
  
  Whenver you have questions on syntax, look at Gallina:
    https://coq.inria.fr/distrib/current/refman/language/gallina-specification-language.html

  BNF diagrams are like string diagrams?
  Something to look at later:https://en.wikipedia.org/wiki/Translational_Backus%E2%80%93Naur_form

  Newlines are parsed(?) but they don't mean anything.

  If problem with syntax, look at ocaml. The thing it is written in.
    Source: http://rigaux.org/language-study/syntax-across-languages-per-language/OCaml.html

 *)


(* Lemma mult_n_Sm : forall n m : nat, n * m + n = n * S m.
Proof.
intros; induction n as [ | p H]; simpl in |- *; auto.
destruct H.
rewrite <- plus_n_Sm.
apply (f_equal S).
pattern m at 1 3 in |-*.
elim m.
all:simpl in |-*.
apply @eq_refl.
intros.
apply f_equal_nat.
apply H.
Qed. *)



(* A pattern is a beta-expansion, inverse of beta-reduction
  Source: https://www.fing.edu.uy/inco/grupos/mf/man/Coq/node.1.2.4.html#@default420
So it is taking a function and putting variables in place?

Beta-reduction is in the land of lambda calculus
Is beta-expansion a more specific domain?
  Take it where it is atm. 

Beta reduction more or less takes something complicated
  and eventually returns something less complicated
I imagine the beta-expansion will take things that aren't
  complicated and eventually return something that is more.
Source: https://ncatlab.org/nlab/show/beta-reduction

at num: literally take the occurences of the variable, count them,
        apply the pattern there.

Most useful thing today: info_auto.
Q:What does @ do?
  Ocaml: list concatenation.
 *)
