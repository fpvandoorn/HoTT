/- Grothendieck Construction of a functor to Cat -/
Require Import Category.Core Functor.Core NaturalTransformation.Core.
Require Import Pseudofunctor.Core Pseudofunctor.FromFunctor.
Require Import Cat.Core.
Require Import Grothendieck.PseudofunctorToCat.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

section Grothendieck
  Context [H : Funext].

  Variable P : PreCategory → Type.
  (*Context [H : ΠC, is_hprop (P C)].*)
  Context {HF : ΠC D, P C → P D → IsHSet (Functor C D)}.

  Local Notation cat := (@sub_pre_cat _ P HF).

  Variable C : PreCategory.
  Variable F : Functor C cat.

  /- Category of elements -/
  definition category : PreCategory :=
       category (F : FunctorToCat).

  /- First projection functor -/
  definition dpr1 : Functor category C :=
       dpr1 (F : FunctorToCat).
End Grothendieck.
