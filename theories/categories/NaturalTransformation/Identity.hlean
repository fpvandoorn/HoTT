/- Identity natural transformation -/
Require Import Category.Core Functor.Core NaturalTransformation.Core NaturalTransformation.Paths.
Require Import PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.
Local Open Scope path_scope.
Local Open Scope natural_transformation_scope.

section identity
  Variable C : PreCategory.
  Variable D : PreCategory.

  /- There is an identity natrual transformation.  We create a number
      of variants, for various uses. -/
  section generalized
    Variables F G : Functor C D.
    Hypothesis HO : object_of F = object_of G.
    Hypothesis HM : transport (λGO, Πs d,
                                           morphism C s d
                                           → morphism D (GO s) (GO d))
                              HO
                              (morphism_of F)
                    = morphism_of G.

    Local Notation CO c := (transport (λGO, morphism D (F c) (GO c))
                                      HO
                                      (identity (F c))).

    definition generalized_identity_commutes s d (m : morphism C s d)
    : CO d ∘ morphism_of F m = morphism_of G m ∘ CO s.
    /-begin
      case HM. case HO.
      exact (left_identity _ _ _ _ ⬝ (right_identity _ _ _ _)⁻¹).
    end-/

    definition generalized_identity_commutes_sym s d (m : morphism C s d)
    : morphism_of G m ∘ CO s = CO d ∘ morphism_of F m.
    /-begin
      case HM. case HO.
      exact (right_identity _ _ _ _ ⬝ (left_identity _ _ _ _)⁻¹).
    end-/

    definition generalized_identity
    : NaturalTransformation F G :=
         Build_NaturalTransformation'
           F G
           (λc, CO c)
           generalized_identity_commutes
           generalized_identity_commutes_sym.
  End generalized.

  Global Arguments generalized_identity_commutes / .
  Global Arguments generalized_identity_commutes_sym / .
  Global Arguments generalized_identity F G !HO !HM / .

  section generalized'
    Variables F G : Functor C D.
    Hypothesis H : F = G.

    definition generalized_identity'
    : NaturalTransformation F G.
    /-begin
      apply (generalized_identity
               F G
               (ap (@object_of C D) H)).
      case H.
      reflexivity.
    end-/
  End generalized'.

  definition identity (F : Functor C D)
  : NaturalTransformation F F :=
       Eval simpl in @generalized_identity F F 1 1.

  Global Arguments generalized_identity' F G !H / .
End identity.

Global Arguments generalized_identity_commutes : simpl never.
Global Arguments generalized_identity_commutes_sym : simpl never.

Module Export NaturalTransformationIdentityNotations.
  Notation "1" := (identity _) : natural_transformation_scope.
End NaturalTransformationIdentityNotations.
