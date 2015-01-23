/- Laws about product categories -/
Require Import Category.Core Functor.Core InitialTerminalCategory.Core InitialTerminalCategory.Functors Category.Prod Functor.Prod Functor.Composition.Core Functor.Identity Functor.Prod.Universal Functor.Composition.Laws Functor.Prod.Universal.
Require Import Functor.Paths.
Require Import Types.Prod Types.ΠHoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope functor_scope.

Local Notation prod_type := Coq.Init.Datatypes.prod.
Local Notation fst_type := Coq.Init.Datatypes.pr1.
Local Notation snd_type := Coq.Init.Datatypes.snd.
Local Notation pair_type := Coq.Init.Datatypes.pair.

/- Swap functor [C × D → D × C] -/
Module Swap.
  definition functor (C D : PreCategory)
  : Functor (C × D) (D × C) :=
       Build_Functor (C × D) (D × C)
                     (λcd, (snd_type cd, fst_type cd)%core)
                     (λ_ _ m, (snd_type m, fst_type m)%core)
                     (λ_ _ _ _ _, refl)
                     (λ_, refl).

  definition law (C D : PreCategory)
  : functor C D ∘ functor D C = 1 :=
       idpath.
End Swap.

/- [A × (B × C) ≅ (A × B) × C] -/
Module Associativity.
  section associativity
    Variable A : PreCategory.
    Variable B : PreCategory.
    Variable C : PreCategory.

    definition functor : Functor (A × (B × C)) ((A × B) × C) :=
         (pr1 × (pr1 ∘ pr2)) × (pr2 ∘ pr2).
    definition inverse : Functor ((A × B) × C) (A × (B × C)) :=
         (pr1 ∘ pr1) × ((pr2 ∘ pr1) × pr2).

    definition law
    : functor ∘ inverse = 1
      /\ inverse ∘ functor = 1 :=
         (refl, refl)%core.
  End associativity.
End Associativity.

/- Laws about the initial category [0] -/
Module Law0.
  section law0
    Context [H : funext].
    Context [H : IsInitialCategory zero].
    Local Notation "0" := zero : category_scope.

    Variable C : PreCategory.

    Global Instance is_initial_category__product
    : IsInitialCategory (C × 0) :=
         λP c, initial_category_ind P (pr2 c).

    Global Instance is_initial_category__product'
    : IsInitialCategory (0 × C) :=
         λP c, initial_category_ind P (pr1 c).

    definition functor : Functor (C × 0) 0 := Functors.from_initial _.
    definition functor' : Functor (0 × C) 0 := Functors.from_initial _.
    definition inverse : Functor 0 (C × 0) := Functors.from_initial _.
    definition inverse' : Functor 0 (0 × C) := Functors.from_initial _.

    /- [C × 0 ≅ 0] -/
    definition law
    : functor ∘ inverse = 1
      /\ inverse ∘ functor = 1 :=
         center _.

    /- [0 × C ≅ 0] -/
    definition law'
    : functor' ∘ inverse' = 1
      /\ inverse' ∘ functor' = 1 :=
         center _.
  End law0.
End Law0.

/- Laws about the terminal category [1] -/
Module Law1.
  section law1
    Context [H : funext].
    Context [H : IsTerminalCategory one].
    Local Notation "1" := one : category_scope.
    Variable C : PreCategory.

    definition functor : Functor (C × 1) C :=
         pr1.

    definition functor' : Functor (1 × C) C :=
         snd.

    definition inverse : Functor C (C × 1) :=
         1 × Functors.to_terminal _.

    definition inverse' : Functor C (1 × C) :=
         Functors.to_terminal _ × 1.

    /- We could throw this in a [repeat match goal with ... end], but
      we know the order, so we hard-code the order to speed it up by a
      factor of about 10. -/

    Local Ltac t_prod :=
      split;
      try first [ exact (compose_fst_prod _ _)
                | exact (compose_snd_prod _ _) ];
      [];
      apply Functor.Prod.Universal.path_prod;
      rewrite <- !Functor.Composition.Laws.associativity by assumption;
      (rewrite ?compose_fst_prod, ?compose_snd_prod,
       ?Functor.Composition.Laws.left_identity,
       ?Functor.Composition.Laws.right_identity
        by assumption);
      try (reflexivity || exact (center _)).

    /- [C × 1 ≅ C] -/
    definition law1
    : functor ∘ inverse = 1
      /\ inverse ∘ functor = 1.
    Proof.
      unfold functor, inverse.
      t_prod.
    Qed.

    /- [1 × C ≅ C] -/
    definition law1'
    : functor' ∘ inverse' = 1
      /\ inverse' ∘ functor' = 1.
    Proof.
      unfold functor', inverse'.
      t_prod.
    Qed.
  End law1.
End Law1.
