/- Category of sections -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Strict.
Require Import Functor.Identity NaturalTransformation.Identity.
Require Import NaturalTransformation.Paths NaturalTransformation.Composition.Core.
Require Import Functor.Paths.
Require Import Types.Record Trunc Types.Sigma.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
Local Open Scope functor_scope.

section FunctorSectionCategory
  Context [H : funext].

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable R : Functor C D.

  /- There is a category [Sect(R)] of sections of [R]. -/

  /- Section of a functor -/
  Record SectionOfFunctor :=
    {
      section_of_functor_morphism :> Functor D C;
      section_of_functor_issect : R ∘ section_of_functor_morphism = 1
    }.

  Local Notation section_of_functor_sigT :=
    { section_of_functor_morphism : Functor D C
    | R ∘ section_of_functor_morphism = 1 }.

  definition section_of_functor_sig
  : section_of_functor_sigT ≃ SectionOfFunctor.
  /-begin
    issig Build_SectionOfFunctor
          section_of_functor_morphism
          section_of_functor_issect.
  end-/

  Local Open Scope natural_transformation_scope.

  /- definition of category of sections of a functor -/
  definition category_of_sections : PreCategory.
  /-begin
    refine (@Build_PreCategory
              SectionOfFunctor
              (λF G, NaturalTransformation F G)
              (λF, 1)
              (λ_ _ _ T U, T ∘ U)
              _
              _
              _
              _);
    abstract (path_natural_transformation; auto with morphism).
  end-/
End FunctorSectionCategory.

definition isstrict_category_of_sections [instance] [H : funext]
      [H : IsStrictCategory C, IsStrictCategory D]
      (F : Functor C D)
: IsStrictCategory (category_of_sections F) | 20.
Proof.
  eapply trunc_equiv; [ | apply section_of_functor_sig ].
  typeclasses eauto.
Qed.
