/- Opposite comma categories -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
Require Import Functor.Composition.Core Functor.Identity Functor.Paths.
Require Import Comma.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.

/- The dual functors [(S / T) ↔ ((Tᵒᵖ / Sᵒᵖ)ᵒᵖ)] -/
section opposite
  section op
    Variable A : PreCategory.
    Variable B : PreCategory.
    Variable C : PreCategory.

    Variable S : Functor A C.
    Variable T : Functor B C.

    Local Notation obj_of x :=
         (CommaCategory.Build_object (T⁻¹op) (S⁻¹op) _ _ (CommaCategory.f x)
          : object ((T⁻¹op / S⁻¹op)⁻¹op)).

    Local Notation mor_of s d m :=
         (CommaCategory.Build_morphism'
            (obj_of d) (obj_of s)
            (CommaCategory.h m%morphism)
            (CommaCategory.g m%morphism)
            (CommaCategory.p_sym m%morphism)
            (CommaCategory.p m%morphism)
          : morphism ((T⁻¹op / S⁻¹op)⁻¹op) (obj_of s) (obj_of d)).

    definition dual_functor : Functor (S / T) ((T⁻¹op / S⁻¹op)⁻¹op) :=
         Build_Functor
           (S / T) ((T⁻¹op / S⁻¹op)⁻¹op)
           (λx, obj_of x)
           (λs d m, mor_of s d m)
           (λ_ _ _ _ _, 1%path)
           (λ_, 1%path).
  End op.

  definition dual_functor_involutive A B C (S : Functor A C) (T : Functor B C)
  : dual_functor S T ∘ (dual_functor T⁻¹op S⁻¹op)⁻¹op = 1
    /\ (dual_functor T⁻¹op S⁻¹op)⁻¹op ∘ dual_functor S T = 1 :=
       (refl, refl)%core.
End opposite.
