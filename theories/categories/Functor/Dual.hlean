/- Opposite functors -/
Require Category.Dual.
Import Category.Dual.CategoryDualNotations.
Require Import Category.Core Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

/- definition of [Fᵒᵖ] -/
definition opposite C D (F : Functor C D) : Functor C⁻¹op D⁻¹op :=
     Build_Functor (C⁻¹op) (D⁻¹op)
                   (object_of F)
                   (λs d, morphism_of F (s := d) (d := s))
                   (λd' d s m1 m2, composition_of F s d d' m2 m1)
                   (identity_of F).

Local Notation "F ⁻¹op" := (opposite F) (at level 3, format "F ⁻¹op") : functor_scope.

Local Open Scope functor_scope.

/- [ᵒᵖ] is judgmentally involutive -/
definition opposite_involutive C D (F : Functor C D) : (F⁻¹op)⁻¹op = F :=
     idpath.

Module Export FunctorDualNotations.
  Notation "F ⁻¹op" := (opposite F) (at level 3, format "F ⁻¹op") : functor_scope.
End FunctorDualNotations.
