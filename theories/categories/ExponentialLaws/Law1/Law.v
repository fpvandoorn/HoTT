/- Exponential laws about the terminal category -/
Require Import Category.Core Functor.Core FunctorCategory.Core Functor.Identity NaturalTransformation.Core Functor.Paths NaturalTransformation.Paths ExponentialLaws.Law1.Functors Functor.Composition.Core.
Require Import InitialTerminalCategory.Core.
Require Import HoTT.Tactics ExponentialLaws.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

/- [C¹ ≅ C] -/
section law1
  Context [H : Funext].
  Context [H : IsInitialCategory zero].
  Context [H : IsTerminalCategory one].
  Local Notation "0" := zero : category_scope.
  Local Notation "1" := one : category_scope.

  Variable C : PreCategory.

  definition helper (c : Functor 1 C)
  : Functors.from_terminal C (c (center _)) ≈ c.
  /-begin
    path_functor.
    exists (path_Π_ _ (λx, ap (object_of c) (contr _))).
    abstract (
        exp_laws_t;
        simpl;
        rewrite <- identity_of;
        f_ap;
        symmetry;
        apply contr
      ).
  end-/

  definition law
  : @functor _ one _ C ∘ inverse C ≈ 1
    /\ inverse C ∘ @functor _ one _ C ≈ 1.
  Proof.
    split;
    path_functor.
    exists (path_Π_ _ helper).
    unfold helper.
    exp_laws_t.
  Qed.
End law1.
