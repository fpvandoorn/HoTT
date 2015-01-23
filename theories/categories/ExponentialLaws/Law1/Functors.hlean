/- Functors involving functor categories involving the terminal category -/
Require Import Category.Core Functor.Core FunctorCategory.Core Functor.Identity NaturalTransformation.Core NaturalTransformation.Paths Functor.Composition.Core.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors InitialTerminalCategory.NaturalTransformations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

section law1
  Context [H : funext].
  Context [H : IsInitialCategory zero].
  Context [H : IsTerminalCategory one].
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  /- [C¹ → C] -/
  definition functor : Functor (1 → C) C :=
       Build_Functor (1 → C) C
                     (λF, F (center _))
                     (λs d m, m (center _))
                     (λ_ _ _ _ _, refl)
                     (λ_, refl).

  definition inverse_morphism_of
             s d (m : morphism C s d)
  : morphism (1 → C)
             (Functors.from_terminal _ s)
             (Functors.from_terminal _ d).
  /-begin
    refine (Build_NaturalTransformation
              (Functors.from_terminal _ s)
              (Functors.from_terminal _ d)
              (λ_, m)
              _).
    simpl; intros.
    etransitivity;
      [ apply right_identity
      | apply symmetry. apply left_identity ].
  end-/

  Global Arguments inverse_morphism_of / _ _ _.

  /- [C → C¹] -/
  definition inverse : Functor C (1 → C).
  /-begin
    refine (Build_Functor
              C (1 → C)
              (@Functors.from_terminal _ _ _ _ _)
              inverse_morphism_of
              _
              _
           );
    abstract (path_natural_transformation; trivial).
  end-/
End law1.

section law1'
  Context [H : funext].
  Context [H : IsInitialCategory zero].
  Context [H : IsTerminalCategory one].
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  Global Instance: IsTerminalCategory (C → 1).

  /- [1ˣ → 1] -/
  definition functor' : Functor (C → 1) 1 :=
       Functors.to_terminal _.

  /- [1 → 1ˣ] -/
  definition inverse' : Functor 1 (C → 1) :=
       Functors.to_terminal _.

  /- [1ˣ ≅ 1] -/
  definition law'
  : functor' ∘ inverse' = 1
    /\ inverse' ∘ functor' = 1 :=
       center _.
End law1'.
