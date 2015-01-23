/- Exponential laws about products and sums in exponents -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import ExponentialLaws.Law2.Functors.
Require Import Functor.Pointwise.Core Functor.Prod.Core.
Require Import Category.Sum Functor.Sum NaturalTransformation.Sum.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Functor.Identity Functor.Composition.Core.
Require Import Types.Prod HoTT.Tactics ExponentialLaws.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

/- [yⁿ⁺ᵐ ≅ yⁿ × yᵐ] -/
section Law2
  Context [H : funext].
  Variable D : PreCategory.
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.



  definition helper1 (c : Functor C1 D × Functor C2 D)
  : ((1 ∘ (Datatypes.pr1 c + Datatypes.snd c) ∘ inl C1 C2)%functor,
     (1 ∘ (Datatypes.pr1 c + Datatypes.snd c) ∘ inr C1 C2)%functor)%core = c.
  /-begin
    apply path_prod; simpl;
    path_functor.
  end-/

  definition helper2_helper (c : Functor (C1 + C2) D) x
  : (1 ∘ c ∘ inl C1 C2 + 1 ∘ c ∘ inr C1 C2) x = c x.
  /-begin
    destruct x; reflexivity.
  end-/

  definition helper2 (c : Functor (C1 + C2) D)
  : 1 ∘ c ∘ inl C1 C2 + 1 ∘ c ∘ inr C1 C2 = c.
  /-begin
    path_functor.
    (exists (path_pi _ _ (@helper2_helper c))).
    abstract exp_laws_t.
  end-/

  definition law
  : functor D C1 C2 ∘ inverse D C1 C2 = 1
    /\ inverse D C1 C2 ∘ functor D C1 C2 = 1.
  Proof.
    split;
    path_functor;
    [ (exists (path_pi _ _ helper1))
    | (exists (path_pi _ _ helper2)) ];
    exp_laws_t;
    unfold helper1, helper2;
    exp_laws_t.
  Qed.
End Law2.
