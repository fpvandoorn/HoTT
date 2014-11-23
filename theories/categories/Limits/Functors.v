/- (co)limits assemble into functors -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import KanExtensions.Core KanExtensions.Functors.
Require Import Limits.Core.
Require Import Adjoint.UniversalMorphisms.
Require Import FunctorCategory.Core.
Require Import Adjoint.Core.
Require Import InitialTerminalCategory.Core NatCategory.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

/- (co)limits assemble into functors -/

Local Open Scope category_scope.

section functors
  Context [H : Funext].
  Variable C : PreCategory.
  Variable D : PreCategory.

  /- Colimit functor, which is left adjoint to Δ -/
  section colimit
    Context `(has_colimits
              : ΠF : Functor D C,
                  @IsColimit _ C D F (colimits F)).

    /- TODO(jgross): We'll probably want to compose this with the
        functor from [1 → C] to [C], and then compose the adjunctions
        similarly.  This will require turning the equality in the
        exponential laws into an adjunction. Probably not very
        hard. -/

    definition colimit_functor : Functor (D → C) (1 → C) :=
         left_kan_extension_functor has_colimits.

    definition colimit_adjunction
    : colimit_functor -| diagonal_functor _ _ :=
         left_kan_extension_adjunction has_colimits.
  End colimit.

  section limit
    Context `(has_limits
              : ΠF : Functor D C,
                  @IsLimit _ C D F (limits F)).

    /- TODO(jgross): We'll probably want to compose this with the
        functor from [1 → C] to [C], and then compose the adjunctions
        similarly.  This will require turning the equality in the
        exponential laws into an adjunction. Probably not very
        hard. -/

    /- Limit functor, which is right adjoint to Δ -/
    definition limit_functor : Functor (D → C) (1 → C) :=
         right_kan_extension_functor has_limits.

    definition limit_adjunction
    : diagonal_functor _ _ -| limit_functor :=
         right_kan_extension_adjunction has_limits.
  End limit.
End functors.
