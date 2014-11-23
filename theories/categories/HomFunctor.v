/- Hom Functor -/
Require Import Category.Core Functor.Core SetCategory.Core Category.Dual Functor.Composition.Core.
Require Category.Prod Functor.Prod.Core.
Import Category.Prod.CategoryProdNotations Functor.Prod.Core.FunctorProdCoreNotations.
Require Import Basics.Overture Basics.Trunc HSet TruncType.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope morphism_scope.

/- definition of [hom : Cᵒᵖ × C → Set] as a functor -/
section hom_functor
  Context [H : Funext].
  Variable C : PreCategory.

  Local Notation obj_of c'c :=
    (BuildhSet
       (morphism
          C
          (fst (c'c : object (C⁻¹op × C)))
          (snd (c'c : object (C⁻¹op × C))))).

  Let hom_functor_morphism_of s's d'd (hf : morphism (C⁻¹op × C) s's d'd)
  : morphism set_cat (obj_of s's) (obj_of d'd) :=
       λg, snd hf ∘ g ∘ fst hf.

  definition hom_functor : Functor (C⁻¹op × C) set_cat.
    refine (Build_Functor (C⁻¹op × C) set_cat
                          (λc'c, obj_of c'c)
                          hom_functor_morphism_of
                          _
                          _);
    subst hom_functor_morphism_of;
    simpl;
    abstract (
        repeat (apply path_Π|| intros [] || intro);
        unfold compose, Overture.compose;
        simpl in *;
        rewrite <- ?associativity, ?left_identity, ?right_identity;
        reflexivity
      ).
  Defined.
End hom_functor.

section covariant_contravariant
  Context [H : Funext].
  Variable C : PreCategory.

  Local Open Scope functor_scope.

  Local Arguments Functor.Prod.Core.induced_snd / .
  Local Arguments Functor.Prod.Core.induced_fst / .

  /- Covariant hom functor [hom_C(A, ─) : C → set] -/
  definition covariant_hom_functor (A : object C⁻¹op) :=
       Eval simpl in Functor.Prod.Core.induced_snd (hom_functor C) A.
  /- Contravariant hom functor [hom_C(─, A) : Cᵒᵖ → set] -/
  definition contravariant_hom_functor (A : C) :=
       Eval simpl in Functor.Prod.Core.induced_fst (hom_functor C) A.
End covariant_contravariant.
