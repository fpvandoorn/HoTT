/- Functors to and from initial and terminal categories -/
Require Import Category.Core Functor.Core Functor.Paths.
Require Import InitialTerminalCategory.Core.
Require Import NatCategory Contractible.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

section functors
  Variable C : PreCategory.

  /- Functor to any terminal category -/
  definition to_terminal [H : @IsTerminalCategory one Hone Hone']
  : Functor C one :=
       Build_Functor
         C one
         (λ_, center _)
         (λ_ _ _, center _)
         (λ_ _ _ _ _, contr _)
         (λ_, contr _).

  /- Constant functor from any terminal category -/
  definition from_terminal [H : @IsTerminalCategory one Hone Hone'] (c : C)
  : Functor one C :=
       Build_Functor
         one C
         (λ_, c)
         (λ_ _ _, identity c)
         (λ_ _ _ _ _, symmetry _ _ (@identity_identity _ _))
         (λ_, idpath).

  /- Functor from any initial category -/
  definition from_initial [H : @IsInitialCategory zero]
  : Functor zero C :=
       Build_Functor
         zero C
         (λx, initial_category_ind _ x)
         (λx _ _, initial_category_ind _ x)
         (λx _ _ _ _, initial_category_ind _ x)
         (λx, initial_category_ind _ x).
End functors.

Local Arguments to_terminal / .
Local Arguments from_terminal / .
Local Arguments from_initial / .

definition to_1 C : Functor C 1 :=
     Eval simpl in to_terminal C.
definition from_1 C c : Functor 1 C :=
     Eval simpl in from_terminal C c.
definition from_0 C : Functor 0 C :=
     Eval simpl in from_initial C.

Local Notation "! x" := (@from_terminal _ terminal_category _ _ _ x) (at level 3, format "'!' x") : functor_scope.

/- Uniqueness principles about initial and terminal categories and functors -/
section unique
  Context [H : Funext].

  Global Instance trunc_initial_category_function
         [H : @IsInitialCategory zero] T
  : is_contr (zero → T) :=
    let x := {| center x := initial_category_ind _ x |} in x.
  /-begin
    intro y.
    apply path_forall; intro x.
    apply (initial_category_ind _ x).
  end-/

  Variable C : PreCategory.

  Global Instance trunc_initial_category
         [H : @IsInitialCategory zero]
  : is_contr (Functor zero C) :=
       let x := {| center := from_initial C |} in x.
  /-begin
    abstract (
        intros; apply path_functor_uncurried;
        (exists (center _));
        apply path_forall; intro x;
        apply (initial_category_ind _ x)
      ).
  end-/

  Global Instance trunc_to_initial_category
         [H : @IsInitialCategory zero]
  : is_hprop (Functor C zero).
  /-begin
    typeclasses eauto.
  Qed.

  definition to_initial_category_empty
             [H : @IsInitialCategory zero]
             (F : Functor C zero)
  : IsInitialCategory C :=
       λP x, initial_category_ind P (F x).

  Global Instance trunc_terminal_category
         [H : @IsTerminalCategory one H0 H1]
  : is_contr (Functor C one) :=
       let x := {| center := to_terminal C |} in x.
  Proof.
    intros.
    exact (center _).
  end-/
End unique.

Module Export InitialTerminalCategoryFunctorsNotations.
  Notation "! x" := (@from_terminal _ terminal_category _ _ _ x) (at level 3, format "'!' x") : functor_scope.
End InitialTerminalCategoryFunctorsNotations.
