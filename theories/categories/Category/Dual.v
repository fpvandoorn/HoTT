/- Opposite Category -/
Require Import Category.Core Category.Objects.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

/- definition of [Cᵒᵖ] -/
definition opposite (C : PreCategory) : PreCategory :=
     @Build_PreCategory'
       C
       (λs d, morphism C d s)
       (identity (C := C))
       (λ_ _ _ m1 m2, m2 ∘ m1)
       (λ_ _ _ _ _ _ _, @associativity_sym _ _ _ _ _ _ _ _)
       (λ_ _ _ _ _ _ _, @associativity _ _ _ _ _ _ _ _)
       (λ_ _, @right_identity _ _ _)
       (λ_ _, @left_identity _ _ _)
       (@identity_identity C)
       _.

Local Notation "C ⁻¹op" := (opposite C) (at level 3, format "C '⁻¹op'") : category_scope.

/- [ᵒᵖ] is judgmentally involutive -/
definition opposite_involutive C : (C⁻¹op)⁻¹op ≈ C := idpath.

/- Initial objects are opposite terminal objects, and vice versa -/
section DualObjects
  Variable C : PreCategory.

  definition terminal_opposite_initial (x : C)
             `(H : IsTerminalObject C x)
  : IsInitialObject (C⁻¹op) x :=
       λx', H x'.

  definition initial_opposite_terminal (x : C)
             `(H : IsInitialObject C x)
  : IsTerminalObject (C⁻¹op) x :=
       λx', H x'.
End DualObjects.

Module Export CategoryDualNotations.
  Notation "C ⁻¹op" := (opposite C) (at level 3, format "C '⁻¹op'") : category_scope.
End CategoryDualNotations.
