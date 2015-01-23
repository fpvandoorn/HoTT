/- Opposite natural transformations -/
Require Category.Dual Functor.Dual.
Import Category.Dual.CategoryDualNotations Functor.Dual.FunctorDualNotations.
Require Import Category.Core Functor.Core NaturalTransformation.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

/- definition of [Tᵒᵖ] -/
definition opposite
           C D
           (F G : Functor C D)
           (T : NaturalTransformation F G)
: NaturalTransformation G⁻¹op F⁻¹op :=
     Build_NaturalTransformation' (G⁻¹op) (F⁻¹op)
                                  (components_of T)
                                  (λs d, commutes_sym T d s)
                                  (λs d, commutes T d s).

Local Notation "T ⁻¹op" := (opposite T) (at level 3, format "T ⁻¹op") : natural_transformation_scope.

/- [ᵒᵖ] is judgmentally involutive -/
Local Open Scope natural_transformation_scope.

definition opposite_involutive C D (F G : Functor C D) (T : NaturalTransformation F G)
: (T⁻¹op)⁻¹op = T :=
     idpath.

Module Export NaturalTransformationDualNotations.
  Notation "T ⁻¹op" := (opposite T) (at level 3, format "T ⁻¹op") : natural_transformation_scope.
End NaturalTransformationDualNotations.
