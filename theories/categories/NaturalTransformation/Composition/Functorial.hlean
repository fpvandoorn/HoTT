/- Functoriality of composition of natural transformations -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import FunctorCategory.Core Functor.Composition.Core NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

section functorial_composition
  Context [H : funext].
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Local Open Scope natural_transformation_scope.

  /- whiskering on the left is a functor -/
  definition whiskerL_functor (F : (D → E)%category)
  : ((C → D) → (C → E))%category :=
       Build_Functor
         (C → D) (C → E)
         (λG, F ∘ G)%functor
         (λ_ _ T, F oL T)
         (λ_ _ _ _ _, composition_of_whisker_l _ _ _)
         (λ_, whisker_l_right_identity _ _).

  /- whiskering on the right is a functor -/
  definition whiskerR_functor (G : (C → D)%category)
  : ((D → E) → (C → E))%category :=
       Build_Functor
         (D → E) (C → E)
         (λF, F ∘ G)%functor
         (λ_ _ T, T oR G)
         (λ_ _ _ _ _, composition_of_whisker_r _ _ _)
         (λ_, whisker_r_left_identity _ _).
End functorial_composition.
