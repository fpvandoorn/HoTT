/- Natural transformations between functors from initial categories and to terminal categories -/
Require Import Category.Core Functor.Core NaturalTransformation.Core Functor.Paths NaturalTransformation.Paths.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Import NatCategory Contractible.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

section NaturalTransformations
  Variable C : PreCategory.

  definition from_initial
             [H : @IsInitialCategory zero] (F G : Functor zero C)
  : NaturalTransformation F G :=
       Build_NaturalTransformation
         F G
         (λx, initial_category_ind _ x)
         (λx _ _, initial_category_ind _ x).

  Global Instance trunc_from_initial
         [H : funext]
         [H : @IsInitialCategory zero] (F G : Functor zero C)
  : is_contr (NaturalTransformation F G) :=
       let x := {| center := from_initial F G |}
       in x.
  /-begin
    abstract (
        intros;
        apply path_natural_transformation;
        intro x;
        exact (initial_category_ind _ x)
      ).
  end-/

  Local Existing Instance Functors.to_initial_category_empty.

  Global Instance trunc_to_initial
         [H : funext]
         [H : @IsInitialCategory zero]
         (F G : Functor zero C)
  : is_contr (NaturalTransformation F G) :=
       trunc_from_initial F G.

  definition to_terminal
             [H : @IsTerminalCategory one H0 H1] (F G : Functor C one)
  : NaturalTransformation F G :=
       Build_NaturalTransformation
         F G
         (λx, center _)
         (λ_ _ _, path_contr _ _).

  Global Instance trunc_to_terminal
         [H : funext]
         [H : @IsTerminalCategory one H0 H1] (F G : Functor C one)
  : is_contr (NaturalTransformation F G) :=
       let x := {| center := to_terminal F G |} in x.
  /-begin
    abstract (path_natural_transformation; exact (contr _)).
  end-/
End NaturalTransformations.
