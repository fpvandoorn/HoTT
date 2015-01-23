/- Opposite adjunction [F ⊣ G → Gᵒᵖ ⊣ Fᵒᵖ] -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
Require Import Adjoint.UnitCounit Adjoint.Core.
Require Import Functor.Identity Functor.Composition.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

/- definition of [Aᵒᵖ] -/
definition opposite
           C D
           (F : Functor C D)
           (G : Functor D C)
           (A : F -| G)
: G⁻¹op -| F⁻¹op :=
     @Build_AdjunctionUnitCounit
       _ _ (G⁻¹op) (F⁻¹op)
       ((counit A)⁻¹op)
       ((unit A)⁻¹op)
       (unit_counit_equation_2 A)
       (unit_counit_equation_1 A).

Local Notation "A ⁻¹op" := (opposite A) (at level 3, format "A '⁻¹op'") : adjunction_scope.

Local Open Scope adjunction_scope.

/- [ᵒᵖ] is judgmentally involutive -/
definition opposite_involutive C D (F : Functor C D) (G : Functor D C) (A : F -| G)
: (A⁻¹op)⁻¹op = A :=
     idpath.

Module Export AdjointDualNotations.
  Notation "A ⁻¹op" := (opposite A) (at level 3, format "A '⁻¹op'") : adjunction_scope.
End AdjointDualNotations.
