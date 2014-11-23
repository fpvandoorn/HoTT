/- Functoriality of product of functors -/
Require Import Category.Core Functor.Core NaturalTransformation.Core Functor.Prod.Core FunctorCategory.Core Category.Prod NaturalTransformation.Prod Functor.Composition.Core NaturalTransformation.Composition.Core.
Require Import NaturalTransformation.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope natural_transformation_scope.

Local Notation fst_type := Coq.Init.Datatypes.pr1.
Local Notation snd_type := Coq.Init.Datatypes.snd.
Local Notation pair_type := Coq.Init.Datatypes.pair.

/- Construction of product of functors as a functor - [_×_ : (C → D) × (C → D') → (C → D × D')] -/
section functorial
  Context [H : Funext].

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable D' : PreCategory.

  definition functor_morphism_of
             s d
             (m : morphism ((C → D) × (C → D')) s d)
  : morphism (_ → _) (pr1 s × pr2 s)%functor (pr1 d × pr2 d)%functor :=
       fst_type m × snd_type m.

  definition functor_composition_of
             s d d'
             (m1 : morphism ((C → D) × (C → D')) s d)
             (m2 : morphism ((C → D) × (C → D')) d d')
  : functor_morphism_of (m2 ∘ m1)
    ≈ functor_morphism_of m2 ∘ functor_morphism_of m1.
  Proof.
    path_natural_transformation; reflexivity.
  Qed.

  definition functor_identity_of
             (x : object ((C → D) × (C → D')))
  : functor_morphism_of (identity x) ≈ identity _.
  Proof.
    path_natural_transformation; reflexivity.
  Qed.

  definition functor
  : object ((C → D) × (C → D') → (C → D × D')) :=
       Build_Functor
          ((C → D) × (C → D')) (C → D × D')
          _
          functor_morphism_of
          functor_composition_of
          functor_identity_of.
End functorial.
