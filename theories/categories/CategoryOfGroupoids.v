/- Groupoid, the precategory of strict groupoid categories -/
Require Import Category.Core Functor.Core Category.Strict.
Require Import Cat.Core.
Require Import GroupoidCategory.Core.
Require Import Functor.Paths.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope functor_scope.

section groupoid_cat
  Context [H : Funext].

  Let P : PreCategory → Type :=
       λC, IsGroupoid C /\ IsStrictCategory C.
  Let HF : ΠC D, P C → P D → IsHSet (Functor C D) :=
       λC D HC HD, @trunc_functor _ C D _ (snd HD) _.

  /- There is a full precategory of [cat] which is the strict groupoid precategories -/

  definition groupoid_cat : PreCategory :=
       @sub_pre_cat _ P HF.
End groupoid_cat.
