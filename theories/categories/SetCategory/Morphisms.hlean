/- Morphisms in [set_cat] -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Category.Morphisms NaturalTransformation.Paths.
Require Import Category.Univalent.
Require Import SetCategory.Core.
Require Import Basics.Overture Basics.Trunc Types.Record Types.Sigma HProp HSet Types.Universe Equivalences HoTT.Misc UnivalenceImpliesfunext TruncType.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

definition isisomorphism_set_cat_natural_transformation_paths
      {fs : funext} (X : set_cat) C D F G
      (T1 T2 : morphism set_cat X (BuildhSet (@NaturalTransformation C D F G)))
      (H : Πx y, T1 x y = T2 x y)
      [H : @IsIsomorphism set_cat _ _ T1]
: @IsIsomorphism set_cat _ _ T2.
/-begin
  exists (T1⁻¹)%morphism;
  abstract (
      first [ apply @iso_moveR_Vp
            | apply @iso_moveR_pV ];
      repeat first [ intro
                   | progress unfold Overture.compose
                   | solve [ auto
                           | apply symmetry. auto ]
                   | apply @path_forall
                   | path_natural_transformation ]
    ).
end-/

section equiv_iso_set_cat
  /- Isomorphisms in [set_cat] are eqivalent to equivalences. -/
  Context [H : funext].

  definition isiso_isequiv s d (m : morphism set_cat s d)
             [H : is_equiv _ _ m]
  : IsIsomorphism m :=
       Build_IsIsomorphism
         set_cat s d
         m m⁻¹%equiv
         (path_pi _ _ (sect m))
         (path_pi _ _ (retr m)).

  definition isequiv_isiso s d (m : morphism set_cat s d)
             [H : IsIsomorphism _ _ _ m]
  : is_equiv m :=
       is_equiv.mk
         _ _
         m m⁻¹%morphism
         (ap10 right_inverse)
         (ap10 left_inverse)
         (λ_, path_ishprop _ _).

  definition iso_equiv (s d : set_cat) (m : s ≃ d)
  : s <~=~> d :=
       Build_Isomorphic
         (@isiso_isequiv s d m _).

  definition isequiv_isiso_isequiv [instance] s d
  : is_equiv (@iso_equiv s d) | 0.
  /-begin
    refine (isequiv_adjointify
              (@iso_equiv s d)
              (λm, equiv.mk _ _ _ (@isequiv_isiso s d m m))
              _
              _);
    simpl in *;
    clear;
    abstract (
        intros [? ?]; simpl;
        unfold iso_equiv; simpl;
        apply ap;
        apply path_ishprop
      ).
  end-/

  definition path_idtoequiv_idtoiso (s d : set_cat) (p : s = d)
  : iso_equiv s d (equiv_path _ _ (ap trunctype_type p)) = idtoiso set_cat p.
  /-begin
    apply path_isomorphic.
    case p.
    reflexivity.
  end-/
End equiv_iso_set_cat.

section equiv_iso_prop_cat
  /- Isomorphisms in [prop_cat] are eqivalent to equivalences. -/
  Context [H : funext].

  definition isiso_isequiv_prop s d (m : morphism prop_cat s d)
             [H : is_equiv _ _ m]
  : IsIsomorphism m :=
       Build_IsIsomorphism
         prop_cat s d
         m m⁻¹%equiv
         (path_pi _ _ (sect m))
         (path_pi _ _ (retr m)).

  definition isequiv_isiso_prop s d (m : morphism prop_cat s d)
             [H : IsIsomorphism _ _ _ m]
  : is_equiv m :=
       is_equiv.mk
         _ _
         m m⁻¹%morphism
         (ap10 right_inverse)
         (ap10 left_inverse)
         (λ_, path_ishprop _ _).

  definition iso_equiv_prop (s d : prop_cat) (m : s ≃ d)
  : s <~=~> d :=
       Build_Isomorphic
         (@isiso_isequiv_prop s d m _).

  definition isequiv_isiso_isequiv_prop [instance] s d
  : is_equiv (@iso_equiv_prop s d) | 0.
  /-begin
    refine (isequiv_adjointify
              (@iso_equiv_prop s d)
              (λm, equiv.mk _ _ _ (@isequiv_isiso_prop s d m _))
              _
              _);
    simpl in *;
    clear;
    abstract (
        intros [? ?]; simpl;
        unfold iso_equiv_prop; simpl;
        apply ap;
        apply path_ishprop
      ).
  end-/

  definition path_idtoequiv_idtoiso_prop (s d : prop_cat) (p : s = d)
  : iso_equiv_prop s d (equiv_path _ _ (ap trunctype_type p)) = idtoiso prop_cat p.
  /-begin
    apply path_isomorphic.
    case p.
    reflexivity.
  end-/
End equiv_iso_prop_cat.

Local Close Scope morphism_scope.
definition iscategory_set_cat [instance] [H : Univalence]
: IsCategory set_cat.
/-begin
  intros C D.
  eapply @isequiv_homotopic; [ | intro; apply path_idtoequiv_idtoiso ].
  change (is_equiv (iso_equiv C D ∘ equiv_path C D ∘ @ap _ _ trunctype_type C D)).
  typeclasses eauto.
end-/

definition iscategory_prop_cat [instance] [H : Univalence]
: IsCategory prop_cat.
/-begin
  intros C D.
  eapply @isequiv_homotopic; [ | intro; apply path_idtoequiv_idtoiso_prop ].
  change (is_equiv (iso_equiv_prop C D ∘ equiv_path C D ∘ @ap _ _ trunctype_type C D)).
  typeclasses eauto.
end-/
