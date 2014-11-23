/- Functors between an exponential of a product and a product of exponentials -/
Require Import Category.Core Functor.Core FunctorCategory.Core Category.Prod.
Require Import Functor.Prod Functor.Composition.Core NaturalTransformation.Composition.Laws NaturalTransformation.Composition.Core.
Require Functor.Prod.Functorial.
Require Import Types.Prod.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.
Local Open Scope functor_scope.

Local Notation fst_type := Coq.Init.Datatypes.fst.
Local Notation snd_type := Coq.Init.Datatypes.snd.
Local Notation pair_type := Coq.Init.Datatypes.pair.

section law3
  Context [H : Funext].
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  /- [(y × z)ⁿ → yⁿ × zⁿ] -/
  definition functor
  : Functor (D → C1 × C2) ((D → C1) × (D → C2)) :=
       Build_Functor
         (D → C1 × C2) ((D → C1) × (D → C2))
         (λH, (fst ∘ H, snd ∘ H)%core)
         (λs d m, (fst oL m, snd oL m)%core)
         (λ_ _ _ _ _, path_prod' (composition_of_whisker_l _ _ _)
                                      (composition_of_whisker_l _ _ _))
         (λ_, path_prod' (whisker_l_right_identity _ _)
                              (whisker_l_right_identity _ _)).

  /- [yⁿ × zⁿ → (y × z)ⁿ] -/
  /- If we had [Require Functor.Functor.], we could just say [Functor.Prod.functor] here. -/
  definition inverse
  : Functor ((D → C1) × (D → C2)) (D → C1 × C2) :=
       Functor.Prod.Functorial.functor _ _ _.
End law3.
