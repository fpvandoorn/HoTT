/- Kan extensions assemble into functors -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import KanExtensions.Core.
Require Import Adjoint.UniversalMorphisms.
Require Import FunctorCategory.Core.
Require Import Adjoint.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

section kan_extension_functors
  Context [H : funext].
  Variable C  : PreCategory.
  Variable C' : PreCategory.
  Variable D  : PreCategory.
  Variable p : object (C → C').

  /- Left Kan extension functor -/
  section lan
    Context `(has_left_kan_extensions
              : Πh : object (C → D),
                  @IsLeftKanExtensionAlong _ _ _ _ p h (left_kan_extensions h)).

    definition left_kan_extension_functor
    : Functor (C → D) (C' → D) :=
         functor__of__initial_morphism has_left_kan_extensions.

    definition left_kan_extension_adjunction
    : left_kan_extension_functor -| pullback_along D p :=
         adjunction__of__initial_morphism has_left_kan_extensions.
  End lan.


  /- Right Kan extension functor -/
  section ran
    Context `(has_right_kan_extensions
              : Πh : object (C → D),
                  @IsRightKanExtensionAlong _ _ _ _ p h (right_kan_extensions h)).

    definition right_kan_extension_functor
    : Functor (C → D) (C' → D) :=
         functor__of__terminal_morphism has_right_kan_extensions.

    definition right_kan_extension_adjunction
    : pullback_along D p -| right_kan_extension_functor :=
         adjunction__of__terminal_morphism has_right_kan_extensions.
  End ran.
End kan_extension_functors.
