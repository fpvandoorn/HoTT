/- Functor category [D → C] (also [Cᴰ] and [[D, C]]) -/
Require Import Category.Core Category.Strict Functor.Core NaturalTransformation.Core Functor.Paths.
/- These must come last, so that [identity], [compose], etc., refer to natural transformations. -/
Require Import NaturalTransformation.Composition.Core NaturalTransformation.Identity NaturalTransformation.Composition.Laws.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

/- definition of [C → D] -/
section functor_category
  Context [H : funext].

  Variable C : PreCategory.
  Variable D : PreCategory.

  /- There is a category Fun(C, D) of functors from [C] to [D]. -/
  definition functor_category : PreCategory :=
       @Build_PreCategory (Functor C D)
                          (@NaturalTransformation C D)
                          (@identity C D)
                          (@compose C D)
                          (@associativity _ C D)
                          (@left_identity _ C D)
                          (@right_identity _ C D)
                          _.
End functor_category.

Local Notation "C → D" := (functor_category C D) : category_scope.

/- [C → D] is a strict category if [D] is -/
definition isstrict_functor_category [H : funext] C [H : IsStrictCategory D]
: IsStrictCategory (C → D).
/-begin
  typeclasses eauto.
end-/

Module Export FunctorCategoryCoreNotations.
  (*Notation "C ⁻¹ D" := (functor_category D C) : category_scope.
  Notation "[ C , D ]" := (functor_category C D) : category_scope.*)
  Notation "C → D" := (functor_category C D) : category_scope.
End FunctorCategoryCoreNotations.
