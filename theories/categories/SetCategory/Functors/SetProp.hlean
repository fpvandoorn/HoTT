/- Functors between [set_cat] and [prop_cat] -/
Require Import Category.Core Functor.Core SetCategory.Core.
Require Import Basics.Trunc HProp HSet TruncType.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

section set_coercions_definitions
  Context [H : funext].

  Variable C : PreCategory.

  definition to_prop := Functor C prop_cat.
  definition to_set := Functor C set_cat.

  definition from_prop := Functor prop_cat C.
  definition from_set := Functor set_cat C.
End set_coercions_definitions.

Identity Coercion to_prop_id : to_prop >-> Functor.
Identity Coercion to_set_id : to_set >-> Functor.
Identity Coercion from_prop_id : from_prop >-> Functor.
Identity Coercion from_set_id : from_set >-> Functor.

section set_coercions
  Context [H : funext].

  Variable C : PreCategory.

  /- Functors to [prop_cat] give rise to functors to [set_cat] -/
  definition to_prop2set (F : to_prop C) : to_set C :=
    Build_Functor C set_cat
                  (λx, BuildhSet (F x))
                  (λs d m, morphism_of F m)
                  (λs d d' m m', composition_of F s d d' m m')
                  (λx, identity_of F x).

  /- Functors from [set_cat] give rise to functors to [prop_cat] -/
  definition from_set2prop (F : from_set C) : from_prop C :=
       Build_Functor prop_cat C
                     (λx, F (BuildhSet x))
                     (λs d m, morphism_of F (m : morphism
                                                        set_cat
                                                        (BuildhSet s)
                                                        (BuildhSet d)))
                     (λs d d' m m', composition_of F
                                                        (BuildhSet s)
                                                        (BuildhSet d)
                                                        (BuildhSet d')
                                                        m
                                                        m')
                     (λx, identity_of F (BuildhSet x)).
End set_coercions.

Coercion to_prop2set : to_prop >-> to_set.
Coercion from_set2prop : from_set >-> from_prop.
