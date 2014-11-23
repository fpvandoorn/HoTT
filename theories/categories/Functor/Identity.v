/- Identity functor -/
Require Import Category.Core Functor.Core.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

section identity
  /- There is an identity functor.  It does the obvious thing. -/
  definition identity C : Functor C C :=
       Build_Functor C C
                     (λx, x)
                     (λ_ _ x, x)
                     (λ_ _ _ _ _, idpath)
                     (λ_, idpath).
End identity.

Module Export FunctorIdentityNotations.
  Notation "1" := (identity _) : functor_scope.
End FunctorIdentityNotations.
