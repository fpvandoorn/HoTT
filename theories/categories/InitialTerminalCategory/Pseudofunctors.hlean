/- Pseudofunctors from initial and terminal categories -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity Functor.Composition.Core.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import Pseudofunctor.Core.
Require Import InitialTerminalCategory.Core.
Require Import FunctorCategory.Morphisms.
Require Import Category.Morphisms.
Require Import NaturalTransformation.Paths.
Require Import NatCategory.
Require Import Contractible PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

section pseudofunctors
  /- Constant functor from any terminal category -/
  definition from_terminal [H : funext] [H : @IsTerminalCategory one Hone Hone']
             (c : PreCategory)
  : Pseudofunctor one.
  /-begin
    refine (Build_Pseudofunctor
              one
              (λ_, c)
              (λ_ _ _, 1%functor)
              (λ_ _ _ _ _, reflexivity _)
              (λ_, reflexivity _)
              _
              _
              _);
      simpl;
      abstract (
          intros;
          path_natural_transformation;
          rewrite ap_const; simpl;
          reflexivity
        ).
  end-/

  /- Functor from any initial category -/
  definition from_initial [H : funext] [H : @IsInitialCategory zero]
  : Pseudofunctor zero :=
       Build_Pseudofunctor
         zero
         (λx, initial_category_ind _ x)
         (λx _ _, initial_category_ind _ x)
         (λx _ _ _ _, initial_category_ind _ x)
         (λx, initial_category_ind _ x)
         (λx, initial_category_ind _ x)
         (λx, initial_category_ind _ x)
         (λx, initial_category_ind _ x).
End pseudofunctors.

Local Arguments from_terminal / .
Local Arguments from_initial / .

definition from_1 [H : funext] c : Pseudofunctor 1 :=
     Eval simpl in from_terminal c.
definition from_0 [H : funext] : Pseudofunctor 0 :=
     Eval simpl in from_initial.

Local Notation "! x" := (@from_terminal _ terminal_category _ _ _ x) (at level 3, format "'!' x") : pseudofunctor_scope.

Module Export InitialTerminalCategoryPseudofunctorsNotations.
  Notation "! x" := (@from_terminal _ terminal_category _ _ _ x) (at level 3, format "'!' x") : pseudofunctor_scope.
End InitialTerminalCategoryPseudofunctorsNotations.
