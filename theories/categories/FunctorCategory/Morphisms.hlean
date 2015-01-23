/- Morphisms in a functor category -/
Require Import Category.Core Functor.Core NaturalTransformation.Paths FunctorCategory.Core Category.Morphisms NaturalTransformation.Core NaturalTransformation.Composition.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope path_scope.
Local Open Scope category_scope.
Local Open Scope morphism_scope.

/- Natural Isomorphisms - isomorphisms in a functor category -/
definition NaturalIsomorphism [H : funext] (C D : PreCategory) F G :=
  @Isomorphic (C → D) F G.

Arguments NaturalIsomorphism {_} [C D] F G / .

definition reflexive_natural_isomorphism [instance] [H : funext] C D
: Reflexive (@NaturalIsomorphism _ C D) | 0 :=
     _.

Coercion natural_transformation_of_natural_isomorphism [H : funext] C D F G
         (T : @NaturalIsomorphism _ C D F G)
: NaturalTransformation F G :=
     T : morphism _ _ _.

Local Infix "<~=~>" := NaturalIsomorphism : natural_transformation_scope.

/- If [T] is an isomorphism, then so is [T x] for any [x] -/
definition isisomorphism_components_of [H : funext]
           [H : @IsIsomorphism (C → D) F G T] x
: IsIsomorphism (T x).
/-begin
  exists (T⁻¹ x).
  - exact (apD10 (ap components_of left_inverse) x).
  - exact (apD10 (ap components_of right_inverse) x).
end-/

Hint Immediate isisomorphism_components_of : typeclass_instances.
/- When one of the functors is the identity functor, we fail to match correctly, because [apply] is stupid.  So we do its work for it. -/
Hint Extern 10 (@IsIsomorphism _ _ _ (@components_of ?C ?D ?F ?G ?T ?x))
=> apply (λH', @isisomorphism_components_of _ C D F G T H' x)
   : typeclass_instances.

definition inverse [H : funext]
           C D (F G : Functor C D) (T : NaturalTransformation F G)
           [H : Πx, IsIsomorphism (T x)]
: NaturalTransformation G F.
/-begin
  exists (λx, (T x)⁻¹);
  abstract (
      intros;
      iso_move_inverse;
      first [ apply commutes
            | apply symmetry. apply commutes ]
    ).
end-/

/- If [T x] is an isomorphism for all [x], then so is [T] -/
definition isisomorphism_natural_transformation [H : funext]
           C D F G (T : NaturalTransformation F G)
           [H : Πx, IsIsomorphism (T x)]
: @IsIsomorphism (C → D) F G T.
/-begin
  exists (inverse _);
  abstract (
      path_natural_transformation;
      first [ apply left_inverse
            | apply right_inverse ]
    ).
end-/

Hint Immediate isisomorphism_natural_transformation : typeclass_instances.

/- Variant of [idtoiso] for natural transformations -/
section idtoiso
  Context [H : funext].
  Variable C : PreCategory.
  Variable D : PreCategory.

  definition idtoiso_natural_transformation
             (F G : object (C → D))
             (T : F = G)
  : NaturalTransformation F G.
  /-begin
    refine (Build_NaturalTransformation'
              F G
              (λx, idtoiso _ (ap10 (ap object_of T) x))
              _
              _);
    intros; case T; simpl;
    [ exact (left_identity _ _ _ _ ⬝ (right_identity _ _ _ _)⁻¹)
    | exact (right_identity _ _ _ _ ⬝ (left_identity _ _ _ _)⁻¹) ].
  end-/

  definition idtoiso
             (F G : object (C → D))
             (T : F = G)
  : F <~=~> G.
  /-begin
    exists (idtoiso_natural_transformation T).
    exists (idtoiso_natural_transformation (T⁻¹)%path);
      abstract (path_natural_transformation; case T; simpl; auto with morphism).
  end-/

  definition eta_idtoiso
        (F G : object (C → D))
        (T : F = G)
  : Morphisms.idtoiso _ T = idtoiso T.
  Proof.
    case T.
    expand; f_ap.
    exact (center _).
  Qed.
End idtoiso.

Module Export FunctorCategoryMorphismsNotations.
  Infix "<~=~>" := NaturalIsomorphism : natural_transformation_scope.
End FunctorCategoryMorphismsNotations.
