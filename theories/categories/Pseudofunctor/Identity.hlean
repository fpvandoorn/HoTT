/- Identity pseudofunctor -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import NaturalTransformation.Isomorphisms.
Require Import NaturalTransformation.Paths.
Require Import Cat.Core.
Require Import Pseudofunctor.Core.

/- Bring things into scope. -/
Import NaturalTransformation.Identity.
Import NaturalTransformation.Composition.Core NaturalTransformation.Composition.Laws.
Import Category.Morphisms.
Import FunctorCategory.Core.

Require Import PathGroupoids.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.

section identity
  Context [H : funext].

  Variable P : PreCategory → Type.
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Local Ltac t :=
    path_natural_transformation;
    abstract (
        autorewrite with functor morphism;
        unfold morphism_isomorphic;
        rewrite ap_idmap, idtoiso_components_of;
        rewrite ?Functor.Composition.Laws.associativity_fst,
        ?Functor.Composition.Laws.left_identity_fst,
        ?Functor.Composition.Laws.right_identity_fst;
        reflexivity
      ).

  definition identity_associativity
        (w x y z : PreCategory) (f : Functor w x)
        (g : Functor x y) (h : Functor y z)
  : associator_1 h g f ∘ (1 oR f ∘ 1) =
    h oL 1 ∘ (1 ∘ @morphism_isomorphic _ _ _ (idtoiso (w → z) (ap idmap (Functor.Composition.Laws.associativity f g h)))).
  /-begin
    t.
  end-/

  definition identity_left_identity
        (x y : PreCategory) (f : Functor x y)
  : 1 oR f ∘ 1 =
    (left_identity_natural_transformation_2 f)
      ∘ @morphism_isomorphic _ _ _ (idtoiso (x → y) (ap idmap (Functor.Composition.Laws.left_identity f))).
  /-begin
    t.
  end-/

  definition identity_right_identity
        (x y : PreCategory) (f : Functor x y)
  : f oL 1 ∘ 1 =
    (right_identity_natural_transformation_2 f)
      ∘ @morphism_isomorphic _ _ _ (idtoiso (x → y) (ap idmap (Functor.Composition.Laws.right_identity f))).
  /-begin
    t.
  end-/

  /- There is an identity pseudofunctor.  It does the obvious thing. -/
  definition identity : Pseudofunctor cat :=
       Build_Pseudofunctor
         cat
         (λC, C.1)
         (λ_ _ F, F)
         (λ_ _ _ _ _, reflexivity _)
         (λ_, reflexivity _)
         (λx y z w, @identity_associativity x.1 y.1 z.1 w.1)
         (λx y, @identity_left_identity x.1 y.1)
         (λx y, @identity_right_identity x.1 y.1).
End identity.

Module Export PseudofunctorIdentityNotations.
  Notation "1" := (identity _) : pseudofunctor_scope.
End PseudofunctorIdentityNotations.
