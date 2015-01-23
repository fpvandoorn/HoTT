/- Dual functor categories -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Dual Functor.Dual NaturalTransformation.Dual.
Require Import Functor.Composition.Core Functor.Identity.
Require Import FunctorCategory.Core.
Require Import Functor.Paths.
Require Import HoTT.Tactics Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

section opposite
  Context [H : funext].

  /- Functors [(C → D) ↔ (Cᵒᵖ → Dᵒᵖ)ᵒᵖ] -/
  definition opposite_functor (C D : PreCategory) : Functor (C → D) (C⁻¹op → D⁻¹op)⁻¹op :=
       Build_Functor
         (C → D) ((C⁻¹op → D⁻¹op)⁻¹op)
         (λF, F⁻¹op)%functor
         (λ_ _ T, T⁻¹op)%natural_transformation
         (λ_ _ _ _ _, refl)
         (λ_, refl).

  Local Ltac op_t C D :=
    split;
    path_functor;
    repeat ⟨apply path_forall, intro⟩;
    simpl;
    destruct_head NaturalTransformation;
    exact idpath.

  /- The above functors are isomorphisms -/
  definition opposite_functor_law C D
  : opposite_functor C D ∘ (opposite_functor C⁻¹op D⁻¹op)⁻¹op = 1
    /\ (opposite_functor C⁻¹op D⁻¹op)⁻¹op ∘ opposite_functor C D = 1.
  Proof.
    op_t C D.
  Qed.
End opposite.
