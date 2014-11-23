/- Natural isomorphisms -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import NaturalTransformation.Composition.Core.
Require Import Functor.Composition.Core.
Require Import Category.Morphisms FunctorCategory.Morphisms.
Require Import FunctorCategory.Core.
Require Import NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.


Local Ltac iso_whisker_t :=
  path_natural_transformation;
  try rewrite <- composition_of, <- identity_of;
  try f_ap;
  match goal with
    | [ H : IsIsomorphism _
        |- context[components_of ?T0 ?x ∘ components_of ?T1 ?x] ]
      => change (T0 x ∘ T1 x)
         with (components_of ((T0 : morphism (_ → _) _ _)
                                ∘ (T1 : morphism (_ → _) _ _))%morphism
                             x);
        progress rewrite ?(@left_inverse _ _ _ _ H), ?(@right_inverse _ _ _ _ H)
  end;
  reflexivity.

section composition
  Context [H : Funext].

  /- Natural isomorphism respects composition -/
  Global Instance isisomorphism_compose
         `(T' : @NaturalTransformation C D F' F'')
         `(T : @NaturalTransformation C D F F')
         [H : @IsIsomorphism (C → D) F' F'' T']
         [H : @IsIsomorphism (C → D) F F' T]
  : @IsIsomorphism (C → D) F F'' (T' ∘ T)%natural_transformation :=
       @isisomorphism_compose (C → D) _ _ T' _ _ T _.

  /- Left whiskering preserves natural isomorphisms -/
  definition iso_whisker_l [instance] C D E
         (F : Functor D E)
         (G G' : Functor C D)
         (T : NaturalTransformation G G')
         [H : @IsIsomorphism (C → D) G G' T]
  : @IsIsomorphism (C → E) (F ∘ G)%functor (F ∘ G')%functor (whisker_l F T).
  /-begin
    exists (whisker_l F (T : morphism (_ → _) _ _)⁻¹);
    abstract iso_whisker_t.
  end-/

  /- Right whiskering preserves natural isomorphisms -/
  definition iso_whisker_r [instance] C D E
         (F F' : Functor D E)
         (T : NaturalTransformation F F')
         (G : Functor C D)
         [H : @IsIsomorphism (D → E) F F' T]
  : @IsIsomorphism (C → E) (F ∘ G)%functor (F' ∘ G)%functor (whisker_r T G).
  /-begin
    exists (whisker_r (T : morphism (_ → _) _ _)⁻¹ G);
    abstract iso_whisker_t.
  end-/

  /- action of [idtoiso] on objects -/
  definition idtoiso_components_of C D
             (F G : Functor C D)
             (T' : F ≈ G)
             x
  : (Category.Morphisms.idtoiso (_ → _) T' : morphism _ _ _) x
    ≈ Category.Morphisms.idtoiso _ (ap10 (ap object_of T') x).
  /-begin
    destruct T'.
    reflexivity.
  end-/

  /- [idtoiso] respsects composition -/
  definition idtoiso_compose C D
         (F F' F'' : Functor C D)
         (T' : F' ≈ F'')
         (T : F ≈ F')
  : ((Category.Morphisms.idtoiso (_ → _) T' : morphism _ _ _)
       ∘ (Category.Morphisms.idtoiso (_ → _) T : morphism _ _ _))%natural_transformation
    ≈ (Category.Morphisms.idtoiso (_ → _) (T ⬝ T')%path : morphism _ _ _).
  /-begin
    path_natural_transformation; path_induction; simpl; auto with morphism.
  end-/

  /- left whiskering respects [idtoiso] -/
  definition idtoiso_whisker_l C D E
         (F : Functor D E)
         (G G' : Functor C D)
         (T : G ≈ G')
  : whisker_l F (Category.Morphisms.idtoiso (_ → _) T : morphism _ _ _)
    ≈ (Category.Morphisms.idtoiso (_ → _) (ap _ T) : morphism _ _ _).
  /-begin
    path_natural_transformation; path_induction; simpl; auto with functor.
  end-/

  /- right whiskering respects [idtoiso] -/
  definition idtoiso_whisker_r C D E
         (F F' : Functor D E)
         (T : F ≈ F')
         (G : Functor C D)
  : whisker_r (Category.Morphisms.idtoiso (_ → _) T : morphism _ _ _) G
    ≈ (Category.Morphisms.idtoiso (_ → _) (ap (λ_, _ ∘ _)%functor T) : morphism _ _ _).
  /-begin
    path_natural_transformation; path_induction; simpl; auto with functor.
  end-/
End composition.

/- Equalities induced by isomorphisms of objects -/
section object_isomorphisms
  definition path_components_of_isisomorphism
        [H : IsIsomorphism C s d m]
        D (F G : Functor C D) (T : NaturalTransformation F G)
  : (G _1 m)⁻¹ ∘ (T d ∘ F _1 m) ≈ T s.
  Proof.
    apply iso_moveR_Vp.
    apply commutes.
  Qed.

  definition path_components_of_isisomorphism'
        [H : IsIsomorphism C s d m]
        D (F G : Functor C D) (T : NaturalTransformation F G)
  : (G _1 m ∘ T s) ∘ (F _1 m)⁻¹ ≈ T d.
  Proof.
    apply iso_moveR_pV.
    symmetry.
    apply commutes.
  Qed.

  definition path_components_of_isomorphic
             `(m : @Isomorphic C s d)
             D (F G : Functor C D) (T : NaturalTransformation F G)
  : (G _1 m)⁻¹ ∘ (T d ∘ F _1 m) ≈ T s :=
       @path_components_of_isisomorphism _ _ _ m m D F G T.

  definition path_components_of_isomorphic'
             `(m : @Isomorphic C s d)
             D (F G : Functor C D) (T : NaturalTransformation F G)
  : (G _1 m ∘ T s) ∘ (F _1 m)⁻¹ ≈ T d :=
       @path_components_of_isisomorphism' _ _ _ m m D F G T.
End object_isomorphisms.
