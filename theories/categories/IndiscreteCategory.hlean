/- Indiscrete category -/
Require Import Category.Core Functor.Core Category.Strict Category.Univalent Category.Morphisms.
Require Import Types.unit Trunc HoTT.Tactics Equivalences.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

/- definition of an indiscrete category -/
Module Export Core.
  section indiscrete_category
    /- The indiscrete category has exactly one morphism between any two
      objects. -/
    Variable X : Type.

    /- We define the symmetrized version of associaitivity differently
      so that the dual of an indiscrete category is convertible with
      the indiscrete category. -/

    definition indiscrete_category : PreCategory :=
         @Build_PreCategory' X
                             (λ_ _, unit)
                             (λ_, star)
                             (λ_ _ _ _ _, star)
                             (λ_ _ _ _ _ _ _, refl)
                             (λ_ _ _ _ _ _ _, refl)
                             (λ_ _ f, match f with star => refl end)
                             (λ_ _ f, match f with star => refl end)
                             (λ_, refl)
                             _.
  End indiscrete_category.

  /- Indiscrete categories are strict categories -/
  definition isstrict_indiscrete_category {H : IsHSet X}
  : IsStrictCategory (indiscrete_category X) :=
       H.

  /- Indiscrete categories are (saturated/univalent) categories -/
  definition iscategory_indiscrete_category [instance] {H : is_hprop X}
  : IsCategory (indiscrete_category X).
  /-begin
    intros.

    eapply (isequiv_adjointify
              (idtoiso (indiscrete_category X) (x := s) (y := d))
              (λ_, center _));
      abstract (
          repeat intro;
          destruct_head_hnf @Isomorphic;
          destruct_head_hnf @IsIsomorphism;
          destruct_head_hnf @unit;
          path_induction_hammer
        ).
  end-/
End Core.

/- Functors to an indiscrete category are given by their action on objects -/
Module Functors.
  section to
    Variable X : Type.
    Variable C : PreCategory.
    Variable objOf : C → X.

    definition to : Functor C (indiscrete_category X) :=
         Build_Functor C (indiscrete_category X)
                       objOf
                       (λ_ _ _, star)
                       (λ_ _ _ _ _, refl)
                       (λ_, refl).
  End to.
End Functors.
