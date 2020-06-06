Require Export Basics.Notations.
(*  
1. Require:
  What:Adds a module to the environment
  How: Not sure.
  Notes:None
  Sources: Coq reference manual 8.9.1 pg 227
2. Export:
  What:Imports the module and dependences
  How: uses import like functions
  Notes: None
  Sources: Coq reference manual 8.9.1 pg 227
3. Basics
  What: Library, has many modules 
  How: field specifcation
  Notes: None
  Sources: Coq reference manual 8.9.1 pg 
4. Notations
  What: Module containing notation, sets precedence and associativity w/out meaning
  How: Mapping?
  Notes: None
  Sources: Coq reference manual 8.9.1 pg 175-176
*)
Local Set Typeclasses Strict Resolution.
(* 
1. Local
  What: Prefix modifier on commands for scope
  How: Dunno
  Notes: Sets the effect of a command to stay within or extend out
  Sources: Coq reference manual 8.10.2 pg 234
2. Set
  What: "Sets flag on"
  How: Dunno
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 220
3. Typeclasses Strict Resolution
  What: Freezes all existentials
  How: Dunno
  Notes: Makes it rigid during unification
  Sources: Coq reference manual 8.10.2 pg 550
*)
Local Unset Elimination Schemes.
(* 
1. Unset
  What: Sets flag off
  How: Dunno
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 220
2. Elimination Schemes
  What: "Allows for automatic declaration of inductive principles when defining a new inductive type"
  How: Dunno
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 481
 *)
Global Set Keyed Unification.
(*
1. Global
  What: "... the global modifier extends the effect outside the module..."
  How: Dunno
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 234
2. Keyed Unification
  What: "Makes hihger-order unification used by rewrite rely on a set of keys to dirve unification."
  How:  A restricted form of rewrite(?)
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 293
*)
Global Unset Strict Universe Declaration.
(*
1. 
  What: "... allows one to freely use identifiers for universes without declaring them first ..."
  How: Dunno
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 605
*)
Global Unset Universe Minimization ToSet.
(*
1. Universe Minimization ToSet
  What: "disallows minimization to the sort Set and only collapses floating universes between themselves"
  How: No fucking clue
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 604
*)
Global Set Default Goal Selector "!".
(*
1. Default Goal Selector "!"
  What: "enforces that all tactics are used either on a single 
        focused goal or with a local selector"
  How: No clue
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 250
*)

Global Set Printing Primitive Projection Parameters.
(*
1. Primitive Projection Parameters
  What: "... reconstructs internally omitted parameters at printing time ..."
  How: No clue
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 140
*)

Global Set Loose Hint Behavior "Strict".
(*
1. Loose Hint Behavior "Strict"
  What: "... changes the behavior of an unloaded hint to an immediate fail 
        tactic, allowing to emulate an import-scoped hint mechanism."
  How: No clue
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 310
*)
Ltac class_apply c := autoapply c with typclass_instances.
(*
1. Ltac
  What: Allows for toplevel definitions
  How: Dunno.
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 344
2. class_apply
  What: Ident(?)
  How: Placement
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 344
3. autoapply
  What: 
    Context: autoapply term with ident
    "applies a term using the transparency information 
    of the hint database ident, and does no typeclass resolution."
  How: Magic.
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 549
4. typclass_instances
  What: A database
  How: No clue
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 548
*)
Definition Relation A: Type := forall _: A, forall _: A, Type.
(*
1. Definition
  What: 
    Context: Definition ident : type := term
      checks and registers ident of being type and bound by term
  How: No clue
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 123
2. ->
  What: "Non dependent product types have a special notation
        A -> B stands forall _ : A, B." 
  How: Rewriting?
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 118
3. ident:term
  What: Binder
  How: pattern matching magic?
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 118
4. Type
  What: 
  How: 
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 175-176
*)




(*
1. 
  What: 
  How: 
  Notes: None
  Sources: Coq reference manual 8.10.2 pg 175-176
*)
