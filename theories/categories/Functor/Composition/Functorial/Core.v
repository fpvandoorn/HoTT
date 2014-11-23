/- Functoriality of functor composition -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import Category.Prod FunctorCategory.Core NaturalTransformation.Composition.Functorial NaturalTransformation.Composition.Laws ExponentialLaws.Law4.Functors.
Require Import NaturalTransformation.Paths.
Require ProductLaws.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

/- Construction of the functor [_∘_ : (C → D) × (D → E) → (C → E)] and it's curried variant -/
section functorial_composition
  Context [H : Funext].
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Local Open Scope natural_transformation_scope.

  definition compose_functor_morphism_of
             s d (m : morphism (C → D) s d)
  : morphism ((D → E) → (C → E))
             (whiskerR_functor _ s)
             (whiskerR_functor _ d) :=
       Build_NaturalTransformation
         (whiskerR_functor E s)
         (whiskerR_functor E d)
         (λx, x oL m)
         (λ_ _ _, exchange_whisker _ _).

  definition compose_functor : object ((C → D) → ((D → E) → (C → E))).
  /-begin
    refine (Build_Functor
              (C → D) ((D → E) → (C → E))
              (@whiskerR_functor _ _ _ _)
              compose_functor_morphism_of
              _
              _);
    abstract (
        path_natural_transformation;
        rewrite ?composition_of, ?identity_of;
        reflexivity
      ).
  end-/

  definition compose_functor_uncurried
  : object ((C → D) × (D → E) → (C → E)) :=
       ExponentialLaws.Law4.Functors.functor _ _ _ compose_functor.

  definition compose_functor' : object ((D → E) → ((C → D) → (C → E))) :=
       ExponentialLaws.Law4.Functors.inverse
         _ _ _ (compose_functor_uncurried ∘ ProductLaws.Swap.functor _ _)%functor.
End functorial_composition.
