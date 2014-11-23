/- Law about currying -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Prod.Core.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Functor.Identity Functor.Composition.Core.
Require Import ExponentialLaws.Law4.Functors.
Require Import Types.Prod HoTT.Tactics Types.ΠBasics.PathGroupoids ExponentialLaws.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

/- [(C₁ × C₂ → D) ≅ (C₁ → (C₂ → D))] -/
section Law4
  Context [H : Funext].
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  Lemma helper1 c
  : functor C1 C2 D (inverse C1 C2 D c) ≈ c.
  /-begin
    path_functor.
    abstract (
        exp_laws_t;
        rewrite <- composition_of;
        exp_laws_t
      ).
  end-/

  Lemma helper2_helper c x
  : inverse C1 C2 D (functor C1 C2 D c) x ≈ c x.
  /-begin
    path_functor.
    abstract exp_laws_t.
  end-/

  Lemma helper2 c
  : inverse C1 C2 D (functor C1 C2 D c) ≈ c.
  /-begin
    path_functor.
    exists (path_Π_ _ (helper2_helper c)).
    abstract (unfold helper2_helper; exp_laws_t).
  end-/

  Lemma law
  : functor C1 C2 D ∘ inverse C1 C2 D ≈ 1
    /\ inverse C1 C2 D ∘ functor C1 C2 D ≈ 1.
  Proof.
    split;
    path_functor;
    [ (exists (path_Π_ _ helper1))
    | (exists (path_Π_ _ helper2)) ];
    unfold helper1, helper2, helper2_helper;
    exp_laws_t.
  Qed.
End Law4.
