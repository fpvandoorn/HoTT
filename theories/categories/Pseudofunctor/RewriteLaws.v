/- Pseudofunctor rewriting helper lemmas -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import FunctorCategory.Core.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import Functor.Composition.Core Functor.Identity.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import NaturalTransformation.Isomorphisms.
Require Import NaturalTransformation.Paths.
Require Import FunctorCategory.Core.
Require Import Pseudofunctor.Core.
Require Import HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

section lemmas
  Local Open Scope natural_transformation_scope.
  Context [H : Funext].

  Variable C : PreCategory.
  Variable F : Pseudofunctor C.

  Lemma p_composition_of_coherent_for_rewrite_helper w x y z
        (f : morphism C w x) (g : morphism C x y) (h : morphism C y z)
        (p p0 p1 p2 : PreCategory) (f0 : morphism C w z → Functor p2 p1)
        (f1 : Functor p0 p1) (f2 : Functor p2 p) (f3 : Functor p p0)
        (f4 : Functor p2 p0) `(@IsIsomorphism (_ → _) f4 (f3 ∘ f2)%functor n)
        `(@IsIsomorphism (_ → _) (f0 (h ∘ (g ∘ f))%morphism) (f1 ∘ f4)%functor n0)
  : @paths (NaturalTransformation _ _)
           (@morphism_isomorphic _ _ _ (Category.Morphisms.idtoiso (p2 → p1) (ap f0 (Category.Core.associativity C w x y z f g h))))
           (n0⁻¹
              ∘ ((f1 oL n⁻¹)
                   ∘ ((f1 oL n)
                        ∘ (n0
                             ∘ (@morphism_isomorphic _ _ _ (Category.Morphisms.idtoiso (p2 → p1) (ap f0 (Category.Core.associativity C w x y z f g h))))))))%natural_transformation.
  /-begin
    simpl in *.
    let C := match goal with |- @paths (@NaturalTransformation ?C ?D ?F ?G) _ _ => constr:(C → D)%category end in
    apply (@iso_moveL_Vp C);
      apply (@iso_moveL_Mp C _ _ _ _ _ _ (iso_whisker_l _ _ _ _ _ _ _)).
    path_natural_transformation.
    reflexivity.
  Qed.

  Arguments p_composition_of_coherent_for_rewrite_helper {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

  section helper
    Context
      {w x y z}
      {f : Functor (F w) (F z)} {f0 : Functor (F w) (F y)}
      {f1 : Functor (F x) (F y)} {f2 : Functor (F y) (F z)}
      {f3 : Functor (F w) (F x)} {f4 : Functor (F x) (F z)}
      {f5 : Functor (F w) (F z)} {n : f5 <~=~> (f4 ∘ f3)%functor}
      {n0 : f4 <~=~> (f2 ∘ f1)%functor} {n1 : f0 <~=~> (f1 ∘ f3)%functor}
      {n2 : f <~=~> (f2 ∘ f0)%functor}.

    Lemma p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper'
    : @IsIsomorphism
        (_ → _) _ _
        (n2 ⁻¹ ∘ (f2 oL n1 ⁻¹ ∘ (associator_1 f2 f1 f3 ∘ (n0 oR f3 ∘ n))))%natural_transformation.
    Proof.
      eapply isisomorphism_compose;
      [ eapply isisomorphism_inverse
      | eapply isisomorphism_compose;
        [ eapply iso_whisker_l; eapply isisomorphism_inverse
        | eapply isisomorphism_compose;
          [ typeclasses eauto
          | eapply isisomorphism_compose;
            [ eapply iso_whisker_r; typeclasses eauto
            | typeclasses eauto ] ] ] ].
    end-/

    definition p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper :=
         Eval hnf in p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper'.

    Local Arguments p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper / .
    Let inv := Eval simpl in @morphism_inverse _ _ _ _ p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper.

    definition p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper__to_inverse
          X
          (H' : X ≈ @Build_Isomorphic (_ → _) _ _ _ p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper)
    : @morphism_inverse _ _ _ _ X ≈ inv :=
         ap (λi, @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i)) H'.
  End helper.

  Lemma p_composition_of_coherent_iso_for_rewrite w x y z
        (f : morphism C w x) (g : morphism C x y) (h : morphism C y z)
  : (Category.Morphisms.idtoiso (_ → _) (ap (@p_morphism_of _ _ F w z) (Category.Core.associativity C w x y z f g h)))
    ≈ @Build_Isomorphic
        (_ → _) _ _
        ((((p_composition_of F w y z h (g ∘ f))⁻¹)
            ∘ ((p_morphism_of F h oL (p_composition_of F w x y g f)⁻¹)
                 ∘ ((associator_1 (p_morphism_of F h) (p_morphism_of F g) (p_morphism_of F f))
                      ∘ ((p_composition_of F x y z h g oR p_morphism_of F f)
                           ∘ p_composition_of F w x z (h ∘ g) f)))))%natural_transformation
        p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper.
  Proof.
    apply path_isomorphic; simpl.
    simpl rewrite (@p_composition_of_coherent _ C F w x y z f g h).
    exact p_composition_of_coherent_for_rewrite_helper.
  Qed.

  Lemma p_left_identity_of_coherent_iso_for_rewrite x y (f : morphism C x y)
  : (Category.Morphisms.idtoiso (_ → _) (ap (@p_morphism_of _ _ F x y) (Category.Core.left_identity C x y f)))
    ≈ @Build_Isomorphic
        (_ → _) _ _
        ((left_identity_natural_transformation_1 (p_morphism_of F f))
           ∘ ((p_identity_of F y oR p_morphism_of F f)
                ∘ p_composition_of F x y y 1 f))%natural_transformation
        _.
  Proof.
    apply path_isomorphic; simpl.
    simpl rewrite (@p_left_identity_of_coherent _ C F x y f).
    path_natural_transformation.
    symmetry.
    etransitivity; apply Category.Core.left_identity.
  Qed.

  Lemma p_right_identity_of_coherent_iso_for_rewrite x y (f : morphism C x y)
  : (Category.Morphisms.idtoiso (_ → _) (ap (@p_morphism_of _ _ F x y) (Category.Core.right_identity C x y f)))
    ≈ @Build_Isomorphic
        (_ → _) _ _
        ((right_identity_natural_transformation_1 (p_morphism_of F f))
           ∘ ((p_morphism_of F f oL p_identity_of F x)
                ∘ p_composition_of F x x y f 1))%natural_transformation
        _.
  Proof.
    apply path_isomorphic; simpl.
    simpl rewrite (@p_right_identity_of_coherent _ C F x y f).
    path_natural_transformation.
    symmetry.
    etransitivity; apply Category.Core.left_identity.
  Qed.

  Local Notation typeof x := ((λT (_ : T), T) _ x) (only parsing).

  Let p_composition_of_coherent_for_rewrite_type w x y z f g h :=
       Eval simpl in typeof (ap (@morphism_isomorphic _ _ _)
                                (@p_composition_of_coherent_iso_for_rewrite w x y z f g h)).
  definition p_composition_of_coherent_for_rewrite w x y z f g h
  : p_composition_of_coherent_for_rewrite_type w x y z f g h :=
       ap (@morphism_isomorphic _ _ _)
          (@p_composition_of_coherent_iso_for_rewrite w x y z f g h).

  Let p_composition_of_coherent_inverse_for_rewrite_type w x y z f g h :=
       Eval simpl in typeof (ap (λi, @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
                                (@p_composition_of_coherent_iso_for_rewrite w x y z f g h)).
  definition p_composition_of_coherent_inverse_for_rewrite w x y z f g h
  : p_composition_of_coherent_inverse_for_rewrite_type w x y z f g h :=
       p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper__to_inverse
         (p_composition_of_coherent_iso_for_rewrite w x y z f g h).

  Let p_left_identity_of_coherent_for_rewrite_type x y f :=
       Eval simpl in typeof (ap (@morphism_isomorphic _ _ _)
                                (@p_left_identity_of_coherent_iso_for_rewrite x y f)).
  definition p_left_identity_of_coherent_for_rewrite x y f
  : p_left_identity_of_coherent_for_rewrite_type x y f :=
       ap (@morphism_isomorphic _ _ _)
          (@p_left_identity_of_coherent_iso_for_rewrite x y f).

  Let p_left_identity_of_coherent_inverse_for_rewrite_type x y f :=
       Eval simpl in typeof (ap (λi, @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
                                (@p_left_identity_of_coherent_iso_for_rewrite x y f)).
  definition p_left_identity_of_coherent_inverse_for_rewrite x y f
  : p_left_identity_of_coherent_inverse_for_rewrite_type x y f :=
       ap (λi, @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
          (@p_left_identity_of_coherent_iso_for_rewrite x y f).

  Let p_right_identity_of_coherent_for_rewrite_type x y f :=
       Eval simpl in typeof (ap (@morphism_isomorphic _ _ _)
                                (@p_right_identity_of_coherent_iso_for_rewrite x y f)).
  definition p_right_identity_of_coherent_for_rewrite x y f
  : p_right_identity_of_coherent_for_rewrite_type x y f :=
       Eval simpl in ap (@morphism_isomorphic _ _ _)
                        (@p_right_identity_of_coherent_iso_for_rewrite x y f).

  Let p_right_identity_of_coherent_inverse_for_rewrite_type x y f :=
       Eval simpl in typeof (ap (λi, @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
                                (@p_right_identity_of_coherent_iso_for_rewrite x y f)).
  definition p_right_identity_of_coherent_inverse_for_rewrite x y f
  : p_right_identity_of_coherent_inverse_for_rewrite_type x y f :=
       ap (λi, @morphism_inverse _ _ _ _ (@isisomorphism_isomorphic _ _ _ i))
          (@p_right_identity_of_coherent_iso_for_rewrite x y f).
End lemmas.
