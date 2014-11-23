/- Identity adjunction [1 ⊣ 1] -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Functor.Identity NaturalTransformation.Identity.
Require Import Adjoint.UnitCounit Adjoint.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

section identity
  /- There is an identity adjunction.  It does the obvious thing. -/

  definition identity C : @Adjunction C C 1 1 :=
       @Build_AdjunctionUnitCounit
         C C 1 1
         1
         1
         (λ_, identity_identity _ _)
         (λ_, identity_identity _ _).
End identity.

Module Export AdjointIdentityNotations.
  Notation "1" := (identity _) : adjunction_scope.
End AdjointIdentityNotations.
