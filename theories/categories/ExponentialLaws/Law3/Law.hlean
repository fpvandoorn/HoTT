/- Laws about an exponential of a product and a product of exponentials -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Prod Functor.Prod.Functorial Functor.Prod.Universal.
Require Import Functor.Paths NaturalTransformation.Paths.
Require Import Functor.Identity Functor.Composition.Core.
Require Import ExponentialLaws.Law3.Functors.
Require Import Types.Prod HoTT.Tactics ExponentialLaws.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

/- [(y × z)ⁿ ≅ yⁿ × zⁿ] -/
section Law3
  Context [H : funext].
  Variable C1 : PreCategory.
  Variable C2 : PreCategory.
  Variable D : PreCategory.

  definition helper (c : Functor D C1 × Functor D C2)
  : ((pr1 ∘ (Datatypes.pr1 c × Datatypes.snd c))%functor,
     (pr2 ∘ (Datatypes.pr1 c × Datatypes.snd c))%functor)%core = c.
  /-begin
    apply path_prod;
    [ apply compose_fst_prod
    | apply compose_snd_prod ].
  end-/

  definition Law
  : functor C1 C2 D ∘ inverse C1 C2 D = 1
    /\ inverse C1 C2 D ∘ functor C1 C2 D = 1.
  Proof.
    split; path_functor;
    [ (exists (path_pi _ _ helper))
    | (exists (path_pi _ _ (λ_, Functor.Prod.Universal.unique refl idpath))) ];
    exp_laws_t;
    unfold helper, compose_fst_prod, compose_snd_prod, Functor.Prod.Universal.unique, Functor.Prod.Universal.unique_helper;
    exp_laws_t.
  Qed.
End Law3.
