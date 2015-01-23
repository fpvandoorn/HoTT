/- Functors between functor categories constructed pointwise -/
Require Import Category.Core Functor.Core FunctorCategory.Core NaturalTransformation.Paths Functor.Composition.Core NaturalTransformation.Core NaturalTransformation.Composition.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.
Local Open Scope functor_scope.

/- This is the on-objects part of the functor-category construction as a functor. -/
section pointwise
  Context [H : funext].

  Variable C : PreCategory.
  Variable C' : PreCategory.
  Variable F : Functor C' C.

  Variable D : PreCategory.
  Variable D' : PreCategory.
  Variable G : Functor D D'.

  Local Notation pointwise_object_of H := (G ∘ H ∘ F : object (C' → D')).
  Local Notation pointwise_whiskerL_object_of H := (G ∘ H : object (C → D')).
  Local Notation pointwise_whiskerR_object_of H := (H ∘ F : object (C' → D)).
/- definition pointwise_object_of : (C → D) → (C' → D') :=
       λH, G ∘ H ∘ F.-/

  definition pointwise_morphism_of s d (m : morphism (C → D) s d)
  : morphism (C' → D')
             (pointwise_object_of s)
             (pointwise_object_of d) :=
         Eval simpl in G oL m oR F.

  definition pointwise_whiskerL_morphism_of s d (m : morphism (C → D) s d)
  : morphism (C → D')
             (pointwise_whiskerL_object_of s)
             (pointwise_whiskerL_object_of d) :=
         Eval simpl in G oL m.

  definition pointwise_whiskerR_morphism_of s d (m : morphism (C → D) s d)
  : morphism (C' → D)
             (pointwise_whiskerR_object_of s)
             (pointwise_whiskerR_object_of d) :=
         Eval simpl in m oR F.

  Global Arguments pointwise_morphism_of _ _ _ / .
  Global Arguments pointwise_whiskerL_morphism_of _ _ _ / .
  Global Arguments pointwise_whiskerR_morphism_of _ _ _ / .

  /- Construction of [pointwise : (C → D) → (C' → D')] from [C' → C] and [D → D'] -/
  definition pointwise : Functor (C → D) (C' → D').
  /-begin
    refine (Build_Functor
              (C → D) (C' → D')
              (λx, pointwise_object_of x)
              pointwise_morphism_of
              _
              _);
    abstract (intros; simpl; path_natural_transformation; auto with functor).
  end-/

  /- Construction of [(C → D) → (C → D')] from [D → D'] -/
  definition pointwise_whiskerL : Functor (C → D) (C → D').
  /-begin
    refine (Build_Functor
              (C → D) (C → D')
              (λx, pointwise_whiskerL_object_of x)
              pointwise_whiskerL_morphism_of
              _
              _);
    abstract (intros; simpl; path_natural_transformation; auto with functor).
  end-/

  /- Construction of [(C → D) → (C' → D)] from [C' → C] -/
  definition pointwise_whiskerR : Functor (C → D) (C' → D).
  /-begin
    refine (Build_Functor
              (C → D) (C' → D)
              (λx, pointwise_whiskerR_object_of x)
              pointwise_whiskerR_morphism_of
              _
              _);
    abstract (intros; simpl; path_natural_transformation; auto with functor).
  end-/
End pointwise.
