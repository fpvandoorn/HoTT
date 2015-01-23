/- definition of pseudonatural transformation -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Pseudofunctor.Core.
Require Import Category.Pi.
Require Import FunctorCategory.Core.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import Functor.Composition.Core Functor.Identity.
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Require Import NaturalTransformation.Identity.
Require Import NaturalTransformation.Isomorphisms.
Require Import NaturalTransformation.Paths.
Require Import FunctorCategory.Core.
Require Import HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Delimit Scope pseudonatural_transformation_scope with pseudonatural_transformation.

Local Open Scope natural_transformation_scope.
Local Open Scope functor_scope.
Local Open Scope morphism_scope.
Local Open Scope pseudonatural_transformation_scope.

/- Quoting Michael Shulman from an email:

    The 2-limit in question is sometimes called a "descent object", or
    the totalization of a truncated cosimplicial object.  It's a
    generalization of an equalizer.  The set of natural
    transformations between two ordinary functors [F],[G : C → D] is
    the equalizer of

    [Π_x D(Fx,Gx) ⇉ Π_{x→y} D(Fx,Gy)]

    The category of pseudonatural transformations between two
    2-functors is the descent object of

    [Π_x D(Fx,Gx) ⇉ Π_{x→y} D(Fx,Gy) ⇛ Π_{x→y→z} D(Fx,Gz)]

    where there are three maps from the second product to the third,
    corresponding to picking out [x→y], [y→z], and [x→z].

    In general, the descent object of

    [A ⇉ B ⇛ C]

    is the category of objects [a∈A] equipped with an isomorphism
    between their two images in [B] which results in a commutative
    triangle between their three images in [C]. -/

/- Later, he said (https://github.com/HoTT/HoTT/pull/382#issuecomment-41240787):

    The "naturality" axiom is only necessary if the domain is a
    2-category rather than a 1-category. However, the respect for
    units axiom really is necessary; I guess I forgot to mention that
    in the email. The way it comes up in the descent object is that
    there's a map from [B] to [A] given by projecting the components
    of identities, and the coherence cell has to become an identity
    when composed with that map. -/

/- We construct the parts as above, but inline the resulting definitions for speed.
<<
Module PseudonaturalTransformationParts.
  section PseudonaturalTransformation
    Context [H : funext].

    Variable X : PreCategory.

    Variables F G : Pseudofunctor X.


    definition A : PreCategory :=
         (Πx : X, F x → G x)%category.
    definition B : PreCategory :=
         (Πx y (m : morphism X x y), F x → G y)%category.
    definition C : PreCategory :=
         (Πx y z (m1 : morphism X y z) (m2 : morphism X x y), F x → G z)%category.

    definition a_part := Eval simpl in object A.

    definition A_to_B_1 : Functor A B.
    /-begin
      refine (Build_Functor
                A B
                (λx__Fx_to_Gx, λx y m, x__Fx_to_Gx y ∘ p_morphism_of F m)%functor
                (λx__s x__d x__m, λx y m, x__m y oR p_morphism_of F m)
                _
                _);
      simpl; repeat (intro || apply path_forall);
      [ apply composition_of_whisker_r
      | apply whisker_r_left_identity ].
    end-/

    definition A_to_B_2 : Functor A B.
    /-begin
      refine (Build_Functor
                A B
                (λx__Fx_to_Gx, λx y m, p_morphism_of G m ∘ x__Fx_to_Gx x)%functor
                (λx__s x__d x__m, λx y m, p_morphism_of G m oL x__m x)
                _
                _);
      simpl; repeat (intro || apply path_forall);
      [ apply composition_of_whisker_l
      | apply whisker_l_right_identity ].
    end-/

    definition b_part (a : a_part) :=
         Eval simpl in Πx y m, (A_to_B_1 a x y m <~=~> A_to_B_2 a x y m).

    definition B_to_A : Functor B A :=
         Build_Functor
           B A
           (λxym__Fx_to_Gy, λx, xym__Fx_to_Gy x x 1)
           (λx__s x__d x__m, λx, x__m x x 1)
           (λ_ _ _ _ _, refl)
           (λ_, refl).

    definition b_id_part (a : a_part) (b : b_part a) :=
         Eval simpl in
          Πx,
            (((left_identity_natural_transformation_1 _)
                ∘ (p_identity_of G _ oR _)
                ∘ (B_to_A _1 b x)
                ∘ (_ oL (p_identity_of F _)⁻¹)
                ∘ (left_identity_natural_transformation_2 _))
             = 1)%natural_transformation.

    definition B_to_C_1 : Functor B C.
    /-begin
      refine (Build_Functor
                B C
                (λxym__Fx_to_Gy, λx y z m1 m2, xym__Fx_to_Gy y z m1 ∘ p_morphism_of F m2)%functor
                (λxym__s xym__d xym__m, λx y z m1 m2, xym__m y z m1 oR p_morphism_of F m2)
                _
                _);
      simpl; repeat (intro || apply path_forall);
      [ apply composition_of_whisker_r
      | apply whisker_r_left_identity ].
    end-/

    definition B_to_C_2 : Functor B C.
    /-begin
      refine (Build_Functor
                B C
                (λxym__Fx_to_Gy, λx y z m1 m2, p_morphism_of G m1 ∘ xym__Fx_to_Gy x y m2)%functor
                (λxym__s xym__d xym__m, λx y z m1 m2, p_morphism_of G m1 oL xym__m x y m2)
                _
                _);
      simpl; repeat (intro || apply path_forall);
      [ apply composition_of_whisker_l
      | apply whisker_l_right_identity ].
    end-/

    definition B_to_C_3 : Functor B C :=
         Build_Functor
           B C
           (λxym__Fx_to_Gy, λx y z m1 m2, xym__Fx_to_Gy x z (m1 ∘ m2))
           (λxym__s xym__d xym__m, λx y z m1 m2, xym__m x z (m1 ∘ m2))
           (λ_ _ _ _ _, refl)
           (λ_, refl).

    definition c_part' (a : a_part) (b : b_part a)
    : Π(x y z : X) (m1 : morphism X y z) (m2 : morphism X x y), Type.
    /-begin
      hnf in a, b.
      pose (λx y m, (b x y m : morphism _ _ _)) as bB; simpl in *.
      intros x y z m1 m2.
      exact (((associator_2 _ _ _)
                ∘ (B_to_C_2 _1 bB x y z m1 m2)
                ∘ (associator_1 _ _ _)
                ∘ (B_to_C_1 _1 bB x y z m1 m2)
                ∘ (associator_2 _ _ _))
             = ((p_composition_of G _ _ _ m1 m2 oR _)
                  ∘ (B_to_C_3 _1 bB x y z m1 m2)
                  ∘ (_ oL (p_composition_of F _ _ _ m1 m2)⁻¹)))%natural_transformation.
    end-/

    Arguments c_part' / .

    definition c_part (a : a_part) (b : b_part a) :=
         Eval simpl in Πx y z m1 m2, @c_part' a b x y z m1 m2.

    /- We would like to define [PseudonaturalTransformation] here, then our types are η-expanded. -/
  (*Record PseudonaturalTransformation :=
      { p_components_of :> a_part;
        p_commutes : b_part p_components_of;
        p_commutes_coherent : c_part p_commutes }.-/
  End PseudonaturalTransformation.
End PseudonaturalTransformationParts.

Print PseudonaturalTransformationParts.a_part.
Print PseudonaturalTransformationParts.b_part.
Print PseudonaturalTransformationParts.b_id_part.
Print PseudonaturalTransformationParts.c_part.
>> *)

Record PseudonaturalTransformation [H : funext] (X : PreCategory)
       (F G : Pseudofunctor X) :=
  { p_components_of
      :> Πa : X, Functor (F a) (G a);
    p_commutes
    : Π(x y : X) (m : morphism X x y),
        ((p_components_of y ∘ p_morphism_of F m)%functor <~=~> (p_morphism_of G m ∘ p_components_of x)%functor)%natural_transformation;
    p_commutes_respects_identity
    : Πx : X,
        ((left_identity_natural_transformation_1 (p_components_of x))
           ∘ (p_identity_of G x oR p_components_of x)
           ∘ (p_commutes x x 1%morphism)
           ∘ (p_components_of x oL (p_identity_of F x) ⁻¹)
           ∘ (right_identity_natural_transformation_2 (p_components_of x))
         = 1)%natural_transformation;
    p_commutes_respects_composition
    : Π(x y z : X) (m1 : morphism X y z) (m2 : morphism X x y),
        (((associator_2 (p_morphism_of G m1) (p_morphism_of G m2) (p_components_of x))
            ∘ (p_morphism_of G m1 oL p_commutes x y m2)
            ∘ (associator_1 (p_morphism_of G m1) (p_components_of y) (p_morphism_of F m2))
            ∘ (p_commutes y z m1 oR p_morphism_of F m2)
            ∘ (associator_2 (p_components_of z) (p_morphism_of F m1) (p_morphism_of F m2)))
         = ((p_composition_of G x y z m1 m2 oR p_components_of x ∘ p_commutes x z (m1 ∘ m2)%morphism)
              ∘ (p_components_of z oL (p_composition_of F x y z m1 m2) ⁻¹)))%natural_transformation }.

Bind Scope pseudonatural_transformation_scope with PseudonaturalTransformation.

Create HintDb pseuodnatural_transformation discriminated.

Arguments p_components_of {_} {X}%category {F G}%pseudofunctor T%pseudonatural_transformation
          a%object : rename, simpl nomatch.

Hint Resolve @p_commutes_respects_identity @p_commutes_respects_composition : category pseudonatural_transformation.
