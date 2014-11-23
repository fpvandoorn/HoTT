/- Universal objects -/
Require Import Category.Core Category.Morphisms.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope morphism_scope.

/- definition of "unique up to unique isomorphism" -/

definition unique_up_to_unique_isomorphism (C : PreCategory) (P : C → Type) :=
  Πx (_ : P x) x' (_ : P x'),
    { c : is_contr (morphism C x x')
    | IsIsomorphism (center (morphism C x x')) }.

/- Terminal objects -/
/- A terminal object is an object with a unique morphism from every
    other object. -/
Notation IsTerminalObject C x :=
  (Πx' : object C, is_contr (morphism C x' x)).

Record TerminalObject (C : PreCategory) :=
  {
    object_terminal :> C;
    isterminal_object_terminal :> IsTerminalObject C object_terminal
  }.

Global Existing Instance isterminal_object_terminal.

/- Initial objects -/
/- An initial object is an object with a unique morphism from every
    other object. -/
Notation IsInitialObject C x :=
  (Πx' : object C, is_contr (morphism C x x')).

Record InitialObject (C : PreCategory) :=
  {
    object_initial :> C;
    isinitial_object_initial :> IsInitialObject C object_initial
  }.

Global Existing Instance isinitial_object_initial.

Arguments unique_up_to_unique_isomorphism [C] P.

/- Initial and terminal objects are unique up to unique isomorphism -/
section CategoryObjectsTheorems
  Variable C : PreCategory.

  Local Ltac unique :=
    repeat first [ intro
                 | exists _
                 | exists (center (morphism C _ _))
                 | etransitivity; [ symmetry | ]; apply contr ].

  /- The terminal object is unique up to unique isomorphism. -/
  Theorem terminal_object_unique
  : unique_up_to_unique_isomorphism (λx, IsTerminalObject C x).
  Proof.
    unique.
  Qed.

  /- The initial object is unique up to unique isomorphism. -/
  Theorem initial_object_unique
  : unique_up_to_unique_isomorphism (λx, IsInitialObject C x).
  Proof.
    unique.
  Qed.
End CategoryObjectsTheorems.
