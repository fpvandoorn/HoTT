/- The functor [ᵒᵖ : cat → cat] -/
Require Import Category.Core Functor.Core.
Require Import Category.Dual Functor.Dual.
Require Import Functor.Composition.Core Functor.Identity.
Require Import Cat.Core Functor.Paths.
Require Import Basics.Trunc Types.Sigma HoTT.Tactics Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.

section opposite
  Context [H : funext].

  Variable P : PreCategory → Type.
  Context [H : ΠC, is_hprop (P C)].
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  Let cat := (@sub_pre_cat _ P HF).

  Hypothesis has_op : ΠC : cat, P C.1⁻¹op.

  definition opposite_functor : Functor cat cat :=
       Build_Functor
         cat cat
         (λC, ⟨C.1⁻¹op, has_op _⟩)
         (λ_ _ F, F⁻¹op)%functor
         (λ_ _ _ _ _, refl)
         (λ_, refl).

  Let opposite_functor_involutive_helper (x : cat)
  : (x.1⁻¹op⁻¹op; has_op ⟨_, has_op _⟩) = x :=
       path_sigma_uncurried
         P
         (((x.1⁻¹op)⁻¹op)%category;
          has_op ((x.1⁻¹op)%category;
                  has_op x))
         x
         (Category.Dual.opposite_involutive x.1;
          path_ishprop _ _).

  Local Open Scope functor_scope.

  Local Arguments path_sigma_uncurried : simpl never.

  definition opposite_functor_involutive
  : opposite_functor ∘ opposite_functor = 1.
  Proof.
    path_functor.
    refine (path_pi _ _ opposite_functor_involutive_helper; _).
    repeat ⟨apply path_forall, intro⟩.
    rewrite !transport_pi_constant.
    transport_path_pi_hammer.
    unfold opposite_functor_involutive_helper.
    rewrite !transport_pr1_path_sigma_uncurried.
    simpl in *.
    repeat progress change (λx, ?f x) with f in *.
    match goal with
      | [ |- context[transport
                          (λx', ?f x'.1 ?y)
                          (@path_sigma_uncurried ?A ?P ?u ?v ?pq)] ]
        => rewrite (@transport_pr1_path_sigma_uncurried
                      A P u v pq
                      (λx, f x y))
    end.
    simpl in *.
    hnf in *.
    subst_body.
    destruct_head @sigT.
    destruct_head @Functor.
    destruct_head @PreCategory.
    reflexivity.
  Qed.
End opposite.
