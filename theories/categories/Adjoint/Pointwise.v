/- Pointwise Adjunctions -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity.
Require Import Category.Morphisms.
Require Import Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import Adjoint.Core Adjoint.UnitCounit Adjoint.UnitCounitCoercions.
Require Import Functor.Pointwise.Core.
Require NaturalTransformation.Pointwise.
Require Functor.Pointwise.Properties.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import FunctorCategory.Core.
Require NaturalTransformation.Identity.
Require NaturalTransformation.Composition.Laws.
Import NaturalTransformation.Identity.NaturalTransformationIdentityNotations.
Require Import NaturalTransformation.Paths Functor.Paths.
Require Import Basics.PathGroupoids HProp Types.ΠHoTT.Tactics Types.Arrow.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

section AdjointPointwise
  Context [H : Funext].

  Variable C : PreCategory.
  Variable D : PreCategory.

  /- [F ⊣ G] → [E⁻¹F ⊣ E⁻¹G] -/
  section l
    Variable E : PreCategory.

    Variable F : Functor C D.
    Variable G : Functor D C.

    Variable A : F -| G.

    definition unit_l
    : NaturalTransformation (identity (E → C))
                            ((pointwise (identity E) G) ∘ (pointwise (identity E) F)).
    /-begin
      pose proof (A : AdjunctionUnit _ _) as A''.
      refine (_ ∘ (((idtoiso (C := (_ → _)) (Functor.Pointwise.Properties.identity_of _ _))⁻¹)%morphism : morphism _ _ _)).
      refine (_ ∘ NaturalTransformation.Pointwise.pointwise_r (Functor.Identity.identity E) (projT1 A'')).
      refine (((idtoiso
                  (C := (_ → _))
                  (Functor.Pointwise.Properties.composition_of
                     (Functor.Identity.identity E) F
                     (Functor.Identity.identity E) G)) : morphism _ _ _)
                ∘ _).
      refine (NaturalTransformation.Pointwise.pointwise_l _ _).
      exact (NaturalTransformation.Composition.Laws.left_identity_natural_transformation_2 _).
    end-/

    definition counit_l
    : NaturalTransformation (pointwise (identity E) F ∘ pointwise (identity E) G)
                            (identity (E → D)).
    /-begin
      pose proof (A : AdjunctionCounit _ _) as A''.
      refine ((((idtoiso (C := (_ → _)) (Functor.Pointwise.Properties.identity_of _ _)))%morphism : morphism _ _ _) ∘ _).
      refine (NaturalTransformation.Pointwise.pointwise_r (Functor.Identity.identity E) (projT1 A'') ∘ _).
      refine (_ o
                (((idtoiso
                     (C := (_ → _))
                     (Functor.Pointwise.Properties.composition_of
                        (Functor.Identity.identity E) G
                        (Functor.Identity.identity E) F))⁻¹)%morphism : morphism _ _ _)).
      refine (NaturalTransformation.Pointwise.pointwise_l _ _).
      exact (NaturalTransformation.Composition.Laws.left_identity_natural_transformation_1 _).
    end-/

    Create HintDb adjoint_pointwise discriminated.
    Hint Rewrite
         identity_of left_identity right_identity
         eta_idtoiso composition_of idtoiso_functor
         @ap_V @ap10_V @ap10_path_forall
         path_functor_uncurried_fst
    : adjoint_pointwise.

    definition pointwise_l : pointwise (identity E) F -| pointwise (identity E) G.
    /-begin
      Time (
          (exists unit_l counit_l);
          abstract (
              path_natural_transformation;
              intros;
              destruct A;
              simpl in *;
                repeat match goal with
                         | _ => progress simpl
                         | _ => progress autorewrite with adjoint_pointwise
                         | [ |- context[ap object_of (path_functor_uncurried ?F ?G ⟨?HO, ?HM⟩)] ]
                           => rewrite (@path_functor_uncurried_fst _ _ _ F G HO HM)
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of_helper
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of_helper
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of_helper_helper
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of_helper_helper
                         | [ H : _ |- _ ] => apply H
                       end
            )
        ). /- 23.345 s -/
    end-/
  End l.

  /- [F ⊣ G] → [Gᴱ ⊣ Fᴱ] -/
  section r
    Variable F : Functor C D.
    Variable G : Functor D C.

    Variable A : F -| G.

    Variable E : PreCategory.

    definition unit_r
    : NaturalTransformation (identity (C → E))
                            ((pointwise F (identity E)) ∘ (pointwise G (identity E))).
    /-begin
      pose proof (A : AdjunctionUnit _ _) as A''.
      refine (_ ∘ (((idtoiso (C := (_ → _)) (Functor.Pointwise.Properties.identity_of _ _))⁻¹)%morphism : morphism _ _ _)).
      refine (_ ∘ NaturalTransformation.Pointwise.pointwise_l (projT1 A'') (Functor.Identity.identity E)).
      refine (((idtoiso
                  (C := (_ → _))
                  (Functor.Pointwise.Properties.composition_of
                     G (Functor.Identity.identity E)
                     F (Functor.Identity.identity E))) : morphism _ _ _)
                ∘ _).
      refine (NaturalTransformation.Pointwise.pointwise_r _ _).
      exact (NaturalTransformation.Composition.Laws.left_identity_natural_transformation_2 _).
    end-/

    definition counit_r
    : NaturalTransformation (pointwise G (identity E) ∘ pointwise F (identity E))
                            (identity (D → E)).
    /-begin
      pose proof (A : AdjunctionCounit _ _) as A''.
      refine ((((idtoiso (C := (_ → _)) (Functor.Pointwise.Properties.identity_of _ _)))%morphism : morphism _ _ _) ∘ _).
      refine (NaturalTransformation.Pointwise.pointwise_l (projT1 A'') (Functor.Identity.identity E) ∘ _).
      refine (_ o
                (((idtoiso
                     (C := (_ → _))
                     (Functor.Pointwise.Properties.composition_of
                        F (Functor.Identity.identity E)
                        G (Functor.Identity.identity E)))⁻¹)%morphism : morphism _ _ _)).
      refine (NaturalTransformation.Pointwise.pointwise_r _ _).
      exact (NaturalTransformation.Composition.Laws.left_identity_natural_transformation_1 _).
    end-/

    Create HintDb adjoint_pointwise discriminated.
    Hint Rewrite
         identity_of left_identity right_identity
         eta_idtoiso composition_of idtoiso_functor
         @ap_V @ap10_V @ap10_path_forall
         path_functor_uncurried_fst
    : adjoint_pointwise.

    definition pointwise_r : pointwise G (identity E) -| pointwise F (identity E).
    /-begin
      Time (
          (exists unit_r counit_r);
          abstract (
              path_natural_transformation;
              intros;
              destruct A;
              simpl in *;
                repeat match goal with
                         | _ => reflexivity
                         | _ => progress simpl
                         | _ => progress autorewrite with adjoint_pointwise
                         | [ |- context[ap object_of (path_functor_uncurried ?F ?G ⟨?HO, ?HM⟩)] ]
                           => rewrite (@path_functor_uncurried_fst _ _ _ F G HO HM)
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of_helper
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of_helper
                         | _ => progress unfold Functor.Pointwise.Properties.identity_of_helper_helper
                         | _ => progress unfold Functor.Pointwise.Properties.composition_of_helper_helper
                         | _ => rewrite <- composition_of; progress rewrite_hyp
                       end
            )
        ). /- 19.097 -/
    end-/
  End r.
End AdjointPointwise.
