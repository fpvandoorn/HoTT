/- Properties of pointwise functors -/
Require Import Category.Core Functor.Core Functor.Pointwise.Core NaturalTransformation.Core NaturalTransformation.Paths Functor.Composition.Core Functor.Identity Functor.Paths.
Require Import PathGroupoids Types.ΠHoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope functor_scope.

section parts
  Context [H : Funext].

  /- We could do this all in a big [repeat match], but we split it
      up, to shave off about two seconds per proof. -/
  Local Ltac functor_pointwise_t helper_lem_match helper_lem :=
    repeat ⟨apply path_forall, intro⟩;
    rewrite !transport_forall_constant, !path_forall_2_beta;
    path_natural_transformation;
    repeat match goal with
             | [ |- context[components_of (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport _ P _ _ _ p (λ_, components_of) z)
           end;
    rewrite !transport_forall_constant;
    transport_to_ap;
    repeat match goal with
             | [ x : _ |- context[ap (λx3 : ?T, ?f (object_of x3 ?z))] ]
               => rewrite (@ap_compose' _ _ _ (λx3' : T, object_of x3') (λOx3, f (Ox3 x)))
             | [ x : _ |- context[ap (λx3 : ?T, ?f (object_of x3 ?z) ?w)] ]
               => rewrite (@ap_compose' _ _ _ (λx3' : T, object_of x3') (λOx3, f (Ox3 x) w))
           end;
    repeat match goal with
             | _ => done
             | [ |- context[λF, @object_of ?C ?D F] ]
               => progress change (λF', @object_of C D F') with (@object_of C D)
             | [ |- context[helper_lem_match ?x] ]
               => rewrite (helper_lem x)
           end.

  /- respects identity -/
  section identity_of
    Variable C : PreCategory.
    Variable D : PreCategory.

    definition identity_of_helper_helper (x : Functor C D)
    : 1 ∘ x ∘ 1 ≈ x.
    /-begin
      path_functor.
    end-/

    definition identity_of_helper_helper_object_of x
    : ap object_of (identity_of_helper_helper x) ≈ idpath :=
         path_functor_uncurried_fst _ _ _.

    definition identity_of_helper
    : (λx : Functor C D, 1 ∘ x ∘ 1) ≈ idmap.
    /-begin
      apply path_forall; intro x.
      apply identity_of_helper_helper.
    end-/

    definition identity_of
    : pointwise (identity C) (identity D) ≈ identity _.
    /-begin
      path_functor.
      exists identity_of_helper.
      unfold identity_of_helper.
      abstract functor_pointwise_t
               identity_of_helper_helper
               identity_of_helper_helper_object_of.
    end-/
  End identity_of.

  /- respects composition -/
  section composition_of
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable C' : PreCategory.
    Variable D' : PreCategory.
    Variable C'' : PreCategory.
    Variable D'' : PreCategory.

    Variable F' : Functor C' C''.
    Variable G : Functor D D'.
    Variable F : Functor C C'.
    Variable G' : Functor D' D''.

    definition composition_of_helper_helper (x : Functor C'' D)
    : G' ∘ G ∘ x ∘ (F' ∘ F) ≈ G' ∘ (G ∘ x ∘ F') ∘ F.
    /-begin
      path_functor.
    end-/

    definition composition_of_helper_helper_object_of x
    : ap object_of (composition_of_helper_helper x) ≈ idpath :=
         path_functor_uncurried_fst _ _ _.

    definition composition_of_helper
    : (λx, G' ∘ G ∘ x ∘ (F' ∘ F)) ≈ (λx, G' ∘ (G ∘ x ∘ F') ∘ F).
    /-begin
      apply path_forall; intro x.
      apply composition_of_helper_helper.
    end-/

    definition composition_of
    : pointwise (F' ∘ F) (G' ∘ G) ≈ pointwise F G' ∘ pointwise F' G.
    /-begin
      path_functor.
      exists composition_of_helper.
      unfold composition_of_helper.
      abstract functor_pointwise_t
               composition_of_helper_helper
               composition_of_helper_helper_object_of.
    end-/
  End composition_of.
End parts.
