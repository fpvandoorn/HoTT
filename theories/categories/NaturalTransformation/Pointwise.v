/- Pointwise Natural Transformations -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import FunctorCategory.Core NaturalTransformation.Paths Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import Functor.Pointwise.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

/- Recall that a "pointwise" functor is a functor [Aᴮ → Cᴰ] induced
    by functors [D → B] and [A → C].  Given two functors [D → B] and a
    natural transformation between them, there is an induced natural
    transformation between the resulting functors between functor
    categories, and similarly for two functors [A → C].  In this file,
    we construct these natural transformations. They will be used to
    construct the pointwise induced adjunction [Fˣ ⊣ Gˣ] of an
    adjunction [F ⊣ G] for all categories [X]. -/

Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.

section pointwise
  Context [H : Funext].

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable C' : PreCategory.
  Variable D' : PreCategory.

  Local Ltac t :=
    path_natural_transformation; simpl;
    rewrite <- ?composition_of;
    try apply ap;
    first [ apply commutes
          | symmetry; apply commutes ].

  /- [Tˣ] for a natural transformation [T : F → G] and a functor [x : C → D] -/
  definition pointwise_l
             (F G : Functor C D)
             (T : NaturalTransformation F G)
             (F' : Functor C' D')
  : NaturalTransformation (pointwise F F') (pointwise G F').
  /-begin
    refine (Build_NaturalTransformation
              (pointwise F F') (pointwise G F')
              (λf : object (D → C'), (F' ∘ f) oL T)%natural_transformation
              _).
    abstract t.
  end-/

  /- [Fᵀ] for a natural transformation [T : F' → G'] and a functor [F : C → D] -/
  definition pointwise_r
             (F : Functor C D)
             (F' G' : Functor C' D')
             (T' : NaturalTransformation F' G')
  : NaturalTransformation (pointwise F F') (pointwise F G').
  /-begin
    refine (Build_NaturalTransformation
              (pointwise F F') (pointwise F G')
              (λf : object (D → C'), T' oR f oR F)%natural_transformation
              _).
    abstract t.
  end-/
End pointwise.
