/- Composition of adjunctions [F' ⊣ G' → F ⊣ G → (F' ∘ F) ⊣ (G ∘ G')] -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import Functor.Identity NaturalTransformation.Identity.
Require NaturalTransformation.Composition.Laws.
Require Import Adjoint.UnitCounit Adjoint.Core.
Require Import Category.Morphisms.
Require Import HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.

/- via the unit+counit+zig+zag definition -/
section compose
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Variable F : Functor C D.
  Variable F' : Functor D E.
  Variable G : Functor D C.
  Variable G' : Functor E D.

  Variable A' : F' -| G'.
  Variable A : F -| G.

  definition compose_unit
  : NaturalTransformation 1 ((G ∘ G') ∘ (F' ∘ F)).
  /-begin
    pose (unit A) as eta.
    pose (unit A') as eta'.
    refine ((fun (T : NaturalTransformation _ _)
                 (U : NaturalTransformation _ _)
             => T ∘ (G oL eta' oR F) ∘ U ∘ eta) _ _);
      NaturalTransformation.Composition.Laws.nt_solve_associator.
  end-/

  definition compose_counit
  : NaturalTransformation ((F' ∘ F) ∘ (G ∘ G')) 1.
  /-begin
    pose (counit A) as eps.
    pose (counit A') as eps'.
    refine ((fun (T : NaturalTransformation _ _)
                 (U : NaturalTransformation _ _)
             => eps' ∘ U ∘ (F' oL eps oR G') ∘ T) _ _);
      NaturalTransformation.Composition.Laws.nt_solve_associator.
  end-/

  definition compose : F' ∘ F -| G ∘ G'.
  /-begin
    exists compose_unit compose_counit;
    simpl;
    abstract (
        repeat
          match goal with
            | _ => intro
            | _ => reflexivity
            | _ => progress rewrite ?identity_of, ?left_identity, ?right_identity
            | _ => rewrite <- ?composition_of, unit_counit_equation_1
            | _ => rewrite <- ?composition_of, unit_counit_equation_2
            | [ A : _ -| _ |- _ = 1%morphism ]
              => (etransitivity; [ | apply (unit_counit_equation_1 A) ];
                  instantiate; try_associativity_quick f_ap)
            | [ A : _ -| _ |- _ = 1%morphism ]
              => (etransitivity; [ | apply (unit_counit_equation_2 A) ];
                  instantiate; try_associativity_quick f_ap)
            | _ => repeat (try_associativity_quick rewrite <- !composition_of);
                  progress repeat apply ap;
                  rewrite ?composition_of
            | [ |- context[components_of ?T] ]
              => (try_associativity_quick simpl rewrite <- (commutes T));
                try_associativity_quick (apply concat_right_identity
                                               || apply concat_left_identity)
            | [ |- context[components_of ?T] ]
              => (try_associativity_quick simpl rewrite (commutes T));
                try_associativity_quick (apply concat_right_identity
                                               || apply concat_left_identity)
          end
      ).
  end-/
End compose.

Module Export AdjointCompositionCoreNotations.
  Infix "o" := compose : adjunction_scope.
End AdjointCompositionCoreNotations.
