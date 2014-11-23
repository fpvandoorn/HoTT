/- PreCategories [set_cat] and [prop_cat] -/
Require Import Category.Core Category.Strict.
Require Import HoTT.Basics.Trunc HProp HSet Types.Universe UnivalenceImpliesFunext TruncType.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Notation cat_of obj :=
  (@Build_PreCategory obj
                      (λx y, x → y)
                      (λ_ x, x)
                      (λ_ _ _ f g, f ∘ g)%core
                      (λ_ _ _ _ _ _ _, idpath)
                      (λ_ _ _, idpath)
                      (λ_ _ _, idpath)
                      _).

/- There is a category [Set], where the objects are sets and the
    morphisms are set morphisms -/

definition prop_cat [H : Funext] : PreCategory := cat_of hProp.
definition set_cat [H : Funext] : PreCategory := cat_of hSet.

/- [Prop] is a strict category -/
definition isstrict_prop_cat [instance] [H : Univalence]
: IsStrictCategory prop_cat :=
     _.
