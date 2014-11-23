/- Projection functors from comma categories -/
Require Import Category.Core Functor.Core.
Require Import Category.Prod Functor.Prod.Core.
Require Import Functor.Composition.Core Functor.Identity.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import Comma.Core.
Require Import Types.Prod.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.
Local Open Scope category_scope.

/- First projection [(S / T) → A × B] (for [S : A → C ← B : T]) -/
section comma_category
  Variable A : PreCategory.
  Variable B : PreCategory.
  Variable C : PreCategory.
  Variable S : Functor A C.
  Variable T : Functor B C.

  definition comma_category_projection : Functor (S / T) (A × B) :=
       Build_Functor
         (S / T) (A × B)
         (λabf, (CommaCategory.a abf, CommaCategory.b abf)%core)
         (λ_ _ m, (CommaCategory.g m, CommaCategory.h m)%core)
         (λ_ _ _ _ _, idpath)
         (λ_, idpath).
End comma_category.

/- First projections [(S / a) → A] and [(a / S) → A] -/
section slice_category
  Variable A : PreCategory.

  Local Arguments Functor.Composition.Core.compose / .
  Local Arguments Functor.Composition.Core.compose_composition_of / .
  Local Arguments Functor.Composition.Core.compose_identity_of / .
  Local Arguments path_prod / .
  Local Arguments path_prod' / .
  Local Arguments path_prod_uncurried / .

  definition arrow_category_projection : Functor (arrow_category A) A :=
       Eval simpl in fst ∘ comma_category_projection _ 1.

  definition slice_category_over_projection (a : A) : Functor (A / a) A :=
       Eval simpl in fst ∘ comma_category_projection 1 _.

  definition coslice_category_over_projection (a : A) : Functor (a \ A) A :=
       Eval simpl in snd ∘ comma_category_projection _ 1.

  section slice_coslice
    Variable C : PreCategory.
    Variable a : C.
    Variable S : Functor A C.

    definition slice_category_projection : Functor (S / a) A :=
         Eval simpl in fst ∘ comma_category_projection S !a.

    definition coslice_category_projection : Functor (a / S) A :=
         Eval simpl in snd ∘ comma_category_projection !a S.
  End slice_coslice.
End slice_category.
